import argparse, os, pathlib, sys
from pysmt.smtlib.parser import Tokenizer

    
AXIOM_FRAC_BOUND = "axiom_frac_bound"
AXIOM_FRAC_ZERO = "axiom_frac_zero"
AXIOM_INT_APPROX = "axiom_int_approximation"
UNINTERP_MOD = "uninterp_mod"
UNINTERP_FRAC = "uninterp_frac"
UNINTERP_ABS = "uninterp_abs"

# Modified method for Tokenizer, changed lines are marked with a "NOTE"
def create_generator(self, reader):
    """Takes a file-like object and produces a stream of tokens following
    the LISP rules.

    This is the method doing the heavy-lifting of tokenization.
    """
    spaces = set([" ", "\n", "\t"])
    separators = set(["(", ")", "|", "\""])
    specials = spaces | separators | set([";", ""])

    try:
        c = next(reader)
        eof = False
        while not eof:
            if c in specials:
                # consume the spaces
                if c in spaces:
                    c = next(reader)

                elif c in separators:
                    if c == "|":
                        s = ["|"]  # NOTE: Changed line
                        c = next(reader)
                        while c and c != "|":
                            if c == "\\": # This is a single '\'
                                c = next(reader)
                                if c != "|" and c != "\\":
                                    # Only \| and \\ are supported escapings
                                    raise PysmtSyntaxError(
                                        "Unknown escaping in quoted symbol: "
                                        "'\\%s'" % c, reader.pos_info)
                            s.append(c)
                            c = next(reader)
                        if not c:
                            raise PysmtSyntaxError("Expected '|'",
                                                   reader.pos_info)
                        s.append("|")  # NOTE: Added line
                        yield "".join(s)
                        c = next(reader)

                    elif c == "\"":
                        # String literals
                        s = c
                        num_quotes = 0
                        while True:
                            c = next(reader)
                            if not c:
                                raise PysmtSyntaxError("Expected '\"'",
                                                       reader.pos_info)

                            if c != "\"" and num_quotes % 2 != 0:
                                break

                            s += c
                            if c == "\"":
                                num_quotes += 1

                        yield s

                    else:
                        yield c
                        c = next(reader)

                elif c == ";":
                    while c and c != "\n":
                        c = next(reader)
                    c = next(reader)

                else:
                    # EOF
                    eof = True
                    assert len(c) == 0
            else:
                tk = []
                while c not in specials:
                    tk.append(c)
                    c = next(reader)
                yield "".join(tk)
    except StopIteration:
        # No more data to read, close generator
        return

Tokenizer.create_generator = create_generator

# Find the smallest number <i> such that `name<i>` does not occur in 'text'
def find_name(text, name):
    if not name in text: return name
    i = 0
    while name + str(i) in text: i += 1
    return name + str(i)

# Find unique names for each axiom and uninterpreted function
def init_names(inputText):
    global AXIOM_FRAC_BOUND, AXIOM_FRAC_ZERO, AXIOM_INT_APPROX, UNINTERP_MOD, UNINTERP_FRAC, UNINTERP_ABS
    AXIOM_FRAC_BOUND = find_name(inputText, AXIOM_FRAC_BOUND)
    AXIOM_FRAC_ZERO = find_name(inputText, AXIOM_FRAC_ZERO)
    AXIOM_INT_APPROX = find_name(inputText, AXIOM_INT_APPROX)
    UNINTERP_MOD = find_name(inputText, UNINTERP_MOD)
    UNINTERP_FRAC = find_name(inputText, UNINTERP_FRAC)
    UNINTERP_ABS = find_name(inputText, UNINTERP_ABS)

# Read one token, translate it, and relax it
def process(tokenizer, level, polarity, savePairs, addSpace=False):
    global hasAbs
    assert level >= 0
    relax = not scriptargs.no_relax_inequality
    t = tokenizer.consume()
    prefix = (" " if not addSpace and t != ")" else "")
    if t == "(":
        level += 1
    elif t == ")":
        level -= 1
    if t == "div":
        prefix += "- (/"
        arg1 = process(tokenizer, 0, None, savePairs)
        arg2 = process(tokenizer, 1, None, savePairs)
        if savePairs: divPairs.add((arg1.strip(), arg2[:-1].strip()))
        prefix += arg1 + arg2 + " (" + UNINTERP_FRAC + arg1 + arg2 + ")"
        level -= 1
    elif t == "*":
        prefix += "*"
        arg1 = process(tokenizer, 0, None, savePairs)
        arg2 = process(tokenizer, 1, None, savePairs)
        if savePairs: mulPairs.add((arg1.strip(), arg2[:-1].strip()))
        prefix += arg1 + arg2
        level -= 1
    elif t == "mod":
        arg1 = process(tokenizer, 0, None, savePairs)
        arg2 = process(tokenizer, 1, None, savePairs)
        if savePairs: divPairs.add((arg1.strip(), arg2[:-1].strip()))
        if not scriptargs.uninterp_mod_simplest:
            prefix += UNINTERP_MOD + arg1 + arg2
        else:
            prefix += "* (" + UNINTERP_FRAC + arg1 + arg2 + arg2
        level -= 1
    elif t == "abs":
        prefix += UNINTERP_ABS
        hasAbs = True
    elif relax and t == "<=" and polarity == False:
        prefix += "< (-" + process(tokenizer, 0, None, savePairs) + " 1)"
    elif relax and t == ">=" and polarity == False:
        prefix += "> (+" + process(tokenizer, 0, None, savePairs) + " 1)"
    elif relax and t == "<" and polarity == True:
        prefix += "<= (+" + process(tokenizer, 0, None, savePairs) + " 1)"
    elif relax and t == ">" and polarity == True:
        prefix += ">= (-" + process(tokenizer, 0, None, savePairs) + " 1)"
    else:
        prefix += t
    if polarity != None:
        if t == "not":
            prefix += process(tokenizer, 1, not polarity, savePairs)
            level -= 1
        elif t == "=>":
            prefix += process(tokenizer, 0, not polarity, savePairs) + process(tokenizer, 1, polarity, savePairs)
            level -= 1
        elif t == "=" or t == "xor":
            prefix += process(tokenizer, 0, None, savePairs) + process(tokenizer, 1, None, savePairs)
            level -= 1
        elif t == "ite":
            prefix += process(tokenizer, 0, not polarity, savePairs) + process(tokenizer, 0, polarity, savePairs) + process(tokenizer, 1, polarity, savePairs)
            level -= 1
        elif not t in ("and", "or", "assert", "(", ")"):
            if t.startswith("define-"): savePairs = False
            if level > 0:
                prefix += process(tokenizer, 1, None, savePairs)
                level -= 1
    return prefix + ("" if level == 0 else process(tokenizer, level, polarity, savePairs, t == "("))

if __name__ == '__main__':
    sys.setrecursionlimit(10000000)
    
    divPairs = set()
    mulPairs = set()
    hasAbs = False
    
    argparser = argparse.ArgumentParser()
    argparser.add_argument("--input_file", type=str, required=True)
    argparser.add_argument("--output_file", type=str, required=True)
    argparser.add_argument("--no_relax_inequality", action='store_true')
    argparser.add_argument("--uninterp_mod_simple", action='store_true')
    argparser.add_argument("--uninterp_mod_simplest", action='store_true')
    argparser.add_argument("--no_frac_zero", action='store_true')
    argparser.add_argument("--no_int_approx", action='store_true')
    scriptargs = argparser.parse_args()

    with open(scriptargs.input_file, "r") as f:
        inputText = " ".join(f.readlines())
    init_names(inputText)
    
    tf = open(scriptargs.input_file, "r")
    tokenizer = Tokenizer(tf, interactive=False)
    
    outputText = []
    lastDe = -1
    firstDe = -1
    ints = set()
    while True:
        try:
            t = tokenizer.consume_maybe()
            if t != "(": raise IOError
            res = "(" + process(tokenizer, 1, True, True, True)
            if firstDe == -1 and res.startswith("(de"): firstDe = len(outputText)
            if res.startswith("(de"): lastDe = len(outputText)
            if (res.startswith("(declare-const ") and res.endswith(" Int)")):
                ints.add(res[15:-5])
            elif (res.startswith("(declare-fun ") and res.endswith(" () Int)")):
                ints.add(res[13:-8])
            elif res.startswith("(set-info :status"): continue
            res = res.replace(" Int", " Real").replace("(Int", "(Real").replace("_NIA", "_UFNRA").replace("NIA", "NRA")
            outputText.append(res)
        except StopIteration:
            break
    tf.close()
    
    assert lastDe >= 0 and firstDe >= 0
    divPairs = sorted(list(divPairs))
    mulPairs = sorted(list(mulPairs))
    
    pathlib.Path(os.path.dirname(scriptargs.output_file)).mkdir(parents=True, exist_ok=True)
    with open(scriptargs.output_file, "w") as f:
        for i in range(len(outputText)):
            if i == firstDe:
                f.write("(declare-fun %s (Real Real) Real)" % UNINTERP_FRAC + os.linesep)
                if len(divPairs):
                    f.write("(define-fun %s ((d1 Real) (d2 Real)) Bool (and (=> (> d2 0) (and (<= 0.0 (%s d1 d2)) (< (%s d1 d2) 1.0))) (=> (< d2 0) (and (>= 0.0 (%s d1 d2)) (> (%s d1 d2) (- 1.0))))))" % (AXIOM_FRAC_BOUND, UNINTERP_FRAC, UNINTERP_FRAC, UNINTERP_FRAC, UNINTERP_FRAC) + os.linesep)
                    if len(mulPairs) > 0 and not scriptargs.no_frac_zero: f.write("(define-fun %s ((d1 Real) (d2 Real) (m1 Real) (m2 Real) (e Real)) Bool (=> (and (= d1 (* m1 m2)) (or (= d2 m1) (= d2 m2))) (= e 0)))" % AXIOM_FRAC_ZERO + os.linesep)
                if not scriptargs.uninterp_mod_simple and not scriptargs.uninterp_mod_simplest:
                    f.write("(define-fun %s ((x Real) (m Real)) Real (ite (and (>= x 0) (< x m)) x (ite (and (>= x m) (< x (+ m m))) (- x m) (ite (and (>= x (- m)) (< x 0)) (+ x m) (* m (%s x m))))))" % (UNINTERP_MOD, UNINTERP_FRAC) + os.linesep)
                elif scriptargs.uninterp_mod_simple:
                    f.write("(define-fun %s ((x Real) (m Real)) Real (ite (and (>= x 0) (< x m)) x (* m (%s x m))))" % (UNINTERP_MOD, UNINTERP_FRAC) + os.linesep)
                if len(ints) > 0 and not scriptargs.no_int_approx: f.write("(define-fun %s ((x Real)) Bool (or (= x 0) (>= x 1) (<= x (- 1))))" % AXIOM_INT_APPROX + os.linesep)
                if hasAbs: f.write("(define-fun %s ((x Real)) Real (ite (>= x 0) x (- x)))" % UNINTERP_ABS + os.linesep)
            if i == lastDe + 1:
                for d in divPairs:
                    f.write("(assert (%s %s %s))" % (AXIOM_FRAC_BOUND, d[0], d[1]) + os.linesep)
                    e = "(" + UNINTERP_FRAC + " " + d[0] + " " + d[1] + ")"
                    if not scriptargs.no_frac_zero:
                        for m in mulPairs:
                            f.write("(assert (%s %s %s %s %s %s))" % (AXIOM_FRAC_ZERO, d[0], d[1], m[0], m[1], e) + os.linesep)
                if not scriptargs.no_int_approx:
                    for c in sorted(list(ints)):
                        f.write("(assert (%s %s))" % (AXIOM_INT_APPROX, c) + os.linesep)
            f.write(outputText[i] + os.linesep)
