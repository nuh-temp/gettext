// -*- Mode: Go; indent-tabs-mode: t -*-

/*
 * Copyright (C) 2015-2016 Canonical Ltd
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use, copy,
 * modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.

 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"io"
	"io/ioutil"
	"log"
	"os"
	"sort"
	"strings"
	"time"
)

var (
	output           = flag.String("output", "", "Output to specified file.")
	addComments      = flag.Bool("add-comments", false, "Place all comment blocks preceding keyword lines in output file.")
	addCommentsTag   = flag.String("add-comments-tag", "", "Place comment blocks starting with TAG and preceding keyword lines in output file.")
	sortOutput       = flag.Bool("sort-output", false, "Generate sorted output.")
	noLocation       = flag.Bool("no-location", false, "Do not write '#: filename:line' lines.")
	msgIDBugsAddress = flag.String("msgid-bugs-address", "EMAIL", "set report address for msgid bugs.")
	packageName      = flag.String("package-name", "", "Set package name in output.")

	keyword           = flag.String("keyword", "gettext.Gettext", "Look for WORD as the keyword for singular strings.")
	keywordPlural     = flag.String("keyword-plural", "gettext.NGettext", "Look for WORD as the keyword for plural strings.")
	keywordContextual = flag.String("keyword-contextual", "gettext.NCGettext", "Look for WORD as the keyword for contextual strings.")

	skipArgs = flag.Int("skip-args", 0, "Number of arguments to skip in gettext function call before considering a text message argument.")

	keywordCfg = flag.String("keyword-cfg", "", "Path to keywords configuration file in JSON format. When given --keyword and --keywordPlural are ignored.")
)

const (
	kTypeSingular   = "singular"
	kTypePlural     = "plural"
	kTypeContextual = "contextual"
)

type keywordDef struct {
	Type     string `json:"type"`
	Name     string `json:"name"`
	SkipArgs int    `json:"skipArgs"`
}

type keywords map[string]*keywordDef

type allKeywordsConfig []*keywordDef

type msgID struct {
	msgidPlural string
	msgctxt     string
	comment     string
	fname       string
	line        int
	formatHint  string
}

var msgIDs map[string][]msgID

func formatComment(com string) string {
	out := ""
	for _, rawline := range strings.Split(com, "\n") {
		line := rawline
		line = strings.TrimPrefix(line, "//")
		line = strings.TrimPrefix(line, "/*")
		line = strings.TrimSuffix(line, "*/")
		line = strings.TrimSpace(line)
		if line != "" {
			out += fmt.Sprintf("#. %s\n", line)
		}
	}

	return out
}

func findCommentsForTranslation(fset *token.FileSet, f *ast.File, posCall token.Position) string {
	com := ""
	for _, cg := range f.Comments {
		// search for all comments in the previous line
		for i := len(cg.List) - 1; i >= 0; i-- {
			c := cg.List[i]

			posComment := fset.Position(c.End())
			//println(posCall.Line, posComment.Line, c.Text)
			if posCall.Line == posComment.Line+1 {
				posCall = posComment
				com = fmt.Sprintf("%s\n%s", c.Text, com)
			}
		}
	}

	// only return if we have a matching prefix
	formatedComment := formatComment(com)
	needle := fmt.Sprintf("#. %s", *addCommentsTag)
	if !strings.HasPrefix(formatedComment, needle) {
		formatedComment = ""
	}

	return formatedComment
}

func constructValue(val interface{}) (string, error) {
	switch val.(type) {
	case *ast.BasicLit:
		return val.(*ast.BasicLit).Value, nil
	// this happens for constructs like:
	//  gettext.Gettext("foo" + "bar")
	case *ast.BinaryExpr:
		// we only support string concat
		if val.(*ast.BinaryExpr).Op != token.ADD {
			return "", nil
		}
		left, err := constructValue(val.(*ast.BinaryExpr).X)
		if err != nil {
			return "", err
		}
		// strip right " (or `)
		left = left[0 : len(left)-1]
		right, err := constructValue(val.(*ast.BinaryExpr).Y)
		if err != nil {
			return "", err
		}
		// strip left " (or `)
		right = right[1:len(right)]
		return left + right, nil
	default:
		return "", fmt.Errorf("unknown type: %v", val)
	}
}

func parseFunExpr(path string, expr ast.Expr) string {
	switch sel := expr.(type) {
	case *ast.Ident:
		if path != "" {
			path = "." + path
		}
		return sel.Name + path
	case *ast.SelectorExpr:
		if path != "" {
			path = "." + path
		}
		return parseFunExpr(sel.Sel.Name+path, sel.X)
	}
	return ""
}

func inspectNodeForTranslations(k keywords, fset *token.FileSet, f *ast.File, n ast.Node) bool {
	switch x := n.(type) {
	case *ast.CallExpr:
		var i18nStr, i18nStrPlural, i18nCtxt string
		var err error
		name := parseFunExpr("", x.Fun)
		if name == "" {
			break
		}
		if keyword, ok := k[name]; ok {
			idx := keyword.SkipArgs
			switch keyword.Type {
			case kTypeSingular:
				i18nStr, err = constructValue(x.Args[idx])
			case kTypePlural:
				i18nStr, err = constructValue(x.Args[idx])
				if err != nil {
					break
				}
				i18nStrPlural, err = constructValue(x.Args[idx+1])
			case kTypeContextual:
				i18nCtxt, err = constructValue(x.Args[idx])
				if err != nil {
					break
				}
				i18nStr, err = constructValue(x.Args[idx+1])
			}
		}
		if err != nil {
			fmt.Fprintf(os.Stderr, "WARN: Unable to obtain value at %s: %v\n", fset.Position(n.Pos()), err)
			break
		}

		if i18nStr == "" {
			break
		}

		// FIXME: too simplistic(?), no %% is considered
		formatHint := ""
		if strings.Contains(i18nStr, "%") || strings.Contains(i18nStrPlural, "%") {
			// well, not quite correct but close enough
			formatHint = "c-format"
		}

		msgidStr := formatI18nStr(i18nStr)
		posCall := fset.Position(n.Pos())
		msgIDs[msgidStr] = append(msgIDs[msgidStr], msgID{
			formatHint:  formatHint,
			msgidPlural: formatI18nStr(i18nStrPlural),
			msgctxt:     formatI18nStr(i18nCtxt),
			fname:       posCall.Filename,
			line:        posCall.Line,
			comment:     findCommentsForTranslation(fset, f, posCall),
		})
	}

	return true
}

func formatI18nStr(s string) string {
	if s == "" {
		return ""
	}
	// the "`" is special
	if s[0] == '`' {
		// replace inner " with \"
		s = strings.Replace(s, "\"", "\\\"", -1)
		// replace \n with \\n
		s = strings.Replace(s, "\n", "\\n", -1)
	}
	// strip leading and trailing " (or `)
	s = s[1 : len(s)-1]
	return s
}

func processFiles(args []string) error {
	// go over the input files
	msgIDs = make(map[string][]msgID)

	fset := token.NewFileSet()
	for _, fname := range args {
		if err := processSingleGoSource(fset, fname); err != nil {
			return err
		}
	}

	return nil
}

func parseKeywords() (keywords, error) {
	k := make(keywords)
	if *keywordCfg != "" {
		data, err := ioutil.ReadFile(*keywordCfg)
		if err != nil {
			return nil, err
		}
		var keywordList []*keywordDef
		if err := json.Unmarshal(data, &keywordList); err != nil {
			return nil, err
		}
		for _, keyword := range keywordList {
			k[keyword.Name] = keyword
		}
	} else {
		k[*keyword] = &keywordDef{
			Type:     kTypeSingular,
			Name:     *keyword,
			SkipArgs: *skipArgs,
		}
		k[*keywordPlural] = &keywordDef{
			Type:     kTypePlural,
			Name:     *keywordPlural,
			SkipArgs: *skipArgs,
		}
		k[*keywordContextual] = &keywordDef{
			Type:     kTypeContextual,
			Name:     *keywordContextual,
			SkipArgs: *skipArgs,
		}
	}
	return k, nil
}

func processSingleGoSource(fset *token.FileSet, fname string) error {
	fnameContent, err := ioutil.ReadFile(fname)
	if err != nil {
		panic(err)
	}

	// Create the AST by parsing src.
	f, err := parser.ParseFile(fset, fname, fnameContent, parser.ParseComments)
	if err != nil {
		panic(err)
	}

	k, err := parseKeywords()
	if err != nil {
		panic(err)
	}

	ast.Inspect(f, func(n ast.Node) bool {
		return inspectNodeForTranslations(k, fset, f, n)
	})

	return nil
}

var formatTime = func() string {
	return time.Now().Format("2006-01-02 15:04-0700")
}

func writePotFile(out io.Writer) {

	header := fmt.Sprintf(`# SOME DESCRIPTIVE TITLE.
# Copyright (C) YEAR THE PACKAGE'S COPYRIGHT HOLDER
# This file is distributed under the same license as the PACKAGE package.
# FIRST AUTHOR <EMAIL@ADDRESS>, YEAR.
#
#, fuzzy
msgid   ""
msgstr  "Project-Id-Version: %s\n"
        "Report-Msgid-Bugs-To: %s\n"
        "POT-Creation-Date: %s\n"
        "PO-Revision-Date: YEAR-MO-DA HO:MI+ZONE\n"
        "Last-Translator: FULL NAME <EMAIL@ADDRESS>\n"
        "Language-Team: LANGUAGE <LL@li.org>\n"
        "Language: \n"
        "MIME-Version: 1.0\n"
        "Content-Type: text/plain; charset=CHARSET\n"
        "Content-Transfer-Encoding: 8bit\n"

`, *packageName, *msgIDBugsAddress, formatTime())
	fmt.Fprintf(out, "%s", header)

	// yes, this is the way to do it in go
	sortedKeys := []string{}
	for k := range msgIDs {
		sortedKeys = append(sortedKeys, k)
	}
	if *sortOutput {
		sort.Strings(sortedKeys)
	}

	// FIXME: use template here?
	for _, k := range sortedKeys {
		msgidList := msgIDs[k]
		for _, msgid := range msgidList {
			if *addComments || *addCommentsTag != "" {
				fmt.Fprintf(out, "%s", msgid.comment)
			}
		}
		if !*noLocation {
			fmt.Fprintf(out, "#:")
			for _, msgid := range msgidList {
				fmt.Fprintf(out, " %s:%d", msgid.fname, msgid.line)
			}
			fmt.Fprintf(out, "\n")
		}
		msgid := msgidList[0]
		if msgid.formatHint != "" {
			fmt.Fprintf(out, "#, %s\n", msgid.formatHint)
		}
		var formatOutput = func(in string) string {
			// split string with \n into multiple lines
			// to make the output nicer
			out := strings.Replace(in, "\\n", "\\n\"\n        \"", -1)
			// cleanup too aggressive splitting (empty "" lines)
			return strings.TrimSuffix(out, "\"\n        \"")
		}
		if msgid.msgctxt != "" {
			fmt.Fprintf(out, "msgctxt \"%v\"\n", formatOutput(msgid.msgctxt))
		}
		fmt.Fprintf(out, "msgid   \"%v\"\n", formatOutput(k))
		if msgid.msgidPlural != "" {
			fmt.Fprintf(out, "msgid_plural   \"%v\"\n", formatOutput(msgid.msgidPlural))
			fmt.Fprintf(out, "msgstr[0]  \"\"\n")
			fmt.Fprintf(out, "msgstr[1]  \"\"\n")
		} else {
			fmt.Fprintf(out, "msgstr  \"\"\n")
		}
		fmt.Fprintf(out, "\n")
	}

}

func main() {
	flag.Parse()
	args := flag.Args()
	if len(args) == 0 {
		fmt.Println("Usage: go-xgettext [options] file1 ...")
		fmt.Println("Options:")
		flag.PrintDefaults()
		os.Exit(0)
	}

	if err := processFiles(args); err != nil {
		log.Fatalf("processFiles failed with: %s", err)
	}

	out := os.Stdout
	if *output != "" {
		var err error
		out, err = os.Create(*output)
		if err != nil {
			log.Fatalf("failed to create %s: %s", *output, err)
		}
	}
	writePotFile(out)
}
