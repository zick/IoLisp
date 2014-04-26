kLPar := 0x28
kRPar := 0x29
kQuote := 0x27

LObj := Object clone
makeLObj := method(tag, data,
  ret := LObj clone
  ret tag := tag
  ret data := data
  ret)

kNil := makeLObj("nil", "nil")

safeCar := method(obj,
  if (obj tag == "cons",
    obj car,
    kNil))

safeCdr := method(obj,
  if (obj tag == "cons",
    obj cdr,
    kNil))

makeError := method(str,
  makeLObj("error", str))

sym_table := Map clone
makeSym := method(str,
  if (str == "nil",
    return kNil)
  if (sym_table hasKey(str) not,
    sym_table atPut(str, makeLObj("sym", str)))
  sym_table at(str))

makeNum := method(num,
  makeLObj("num", num))

makeCons := method(a, d,
  cell := LObj clone
  cell tag := "cons"
  cell car := a
  cell cdr := d
  cell)

makeSubr := method(fn,
  makeLObj("subr", fn))

makeExpr := method(args, env,
  expr := LObj clone
  expr tag := "expr"
  expr args := safeCar(args)
  expr body := safeCdr(args)
  expr env := env
  expr)

nreverse := method(lst,
  ret := kNil
  while (lst tag == "cons",
    tmp := lst cdr
    lst cdr := ret
    ret := lst
    lst := tmp)
  ret)

pairlis := method(lst1, lst2,
  ret := kNil
  while (lst1 tag == "cons" and lst2 tag == "cons",
    ret := makeCons(makeCons(lst1 car, lst2 car), ret)
    lst1 := lst1 cdr
    lst2 := lst2 cdr)
  nreverse(ret))

isSpace := method(c,
  c == 0x09 or c == 0x0a or c == 0x0d or c == 0x20)  // '\t', '\r', '\n', ' '

isDelimiter := method(c,
  c == kLPar or c == kRPar or c == kQuote or isSpace(c))

skipSpaces := method(str,
  i := 0
  while (i < str size and isSpace(str at(i)),
    i := i + 1)
  str exSlice(i))

isNumChar := method(c,
  0x30 <= c and c <= 0x39)  // '0' <= c <= '9'

toNum := method(c,
  c - 0x30)  // c - '0'

makeNumOrSym := method(str,
  i := 0
  sign := 1
  if (str at(0) == 0x2d,  // '-'
    sign := -1
    i := 1)
  is_num := false
  num := 0
  while (i < str size,
    c := str at(i)
    if (isNumChar(c),
      // then
      is_num := true
      num := num * 10 + toNum(c)
      i := i + 1,
      // else
       is_num := false
       break))
  if (is_num,
    makeNum(num * sign),
    makeSym(str)))

readAtom := method(str,
  next := ""
  for (i, 0, str size - 1,
    if (isDelimiter(str at(i)),
      next := str exSlice(i)
      str := str exSlice(0, i)
      break))
  list(makeNumOrSym(str), next))

read := method(str,
  str := skipSpaces(str)
  if (str size == 0,
    return list(makeError("empty input"), ""))
  c := str at(0)
  if (c == kRPar,
    return list(makeError("invalid syntax: " with(str)), ""))
  if (c == kLPar,
    return readList(str exSlice(1)))
  if (c == kQuote,
    tmp := read(str exSlice(1))
    return list(makeCons(makeSym("quote"), makeCons(tmp at(0), kNil)),
                tmp at(1)))
  return readAtom(str))

readList := method(str,
  ret := kNil
  while (true,
    str := skipSpaces(str)
    if (str size == 0,
      return list(makeError("unfinished parenthesis"), ""))
    if (str at(0) == kRPar,
      break)
    tmp := read(str)
    elm := tmp at(0)
    next := tmp at(1)
    if (elm tag == "error",
      return list(elm, ""))
    ret := makeCons(elm, ret)
    str := next)
  list(nreverse(ret), str exSlice(1)))

printObj := method(obj,
  tag := obj tag
  if (tag == "num" or tag == "sym" or tag == "nil",
    return obj data asString)
  if (tag == "error",
    return "<error: " with(obj data, ">"))
  if (tag == "cons",
    return printList(obj))
  if (tag == "subr" or tag == "expr",
    return "<" with(tag, ">"))
  return "<unknown>")

printList := method(obj,
  ret := ""
  first := true
  while (obj tag == "cons",
    if (first,
      // then
      ret := printObj(obj car)
      first = false,
      // else
      ret := ret with(" ", printObj(obj car)))
    obj := obj cdr)
  if (obj == kNil,
    "(" with(ret, ")"),
    "(" with(ret, " . ", printObj(obj), ")")))

findVar := method(sym, env,
  while (env tag == "cons",
    alist := env car
    while (alist tag == "cons",
      if (alist car car == sym,
        return alist car)
      alist := alist cdr)
    env := env cdr)
  return kNil)

g_env := makeCons(kNil, kNil)

addToEnv := method(sym, val, env,
  env car := makeCons(makeCons(sym, val), env car))

eval := method(obj, env,
  tag := obj tag
  if (tag == "nil" or tag == "num" or tag == "error",
    return obj)
  if (tag == "sym",
    bind := findVar(obj, env)
    if (bind == kNil,
      return makeError(obj data with(" has no value")),
      return bind cdr))
  op := safeCar(obj)
  args := safeCdr(obj)
  if (op == makeSym("quote"),
    return safeCar(args))
  if (op == makeSym("if"),
    if (eval(safeCar(args), env) == kNil,
      return eval(safeCar(safeCdr(safeCdr(args))), env),
      return eval(safeCar(safeCdr(args)), env)))
  if (op == makeSym("lambda"),
    return makeExpr(args, env))
  if (op == makeSym("defun"),
    expr := makeExpr(safeCdr(args), env)
    sym := safeCar(args)
    addToEnv(sym, expr, g_env)
    return sym)
  apply(eval(op, env), evlis(args, env), env))

evlis := method(lst, env,
  ret := kNil
  while (lst tag == "cons",
    elm := eval(lst car, env)
    if (elm tag == "error",
      return elm)
    ret := makeCons(elm, ret)
    lst := lst cdr)
  nreverse(ret))

progn := method(body, env,
  ret := kNil
  while (body tag == "cons",
    ret := eval(body car, env)
    body := body cdr)
  ret)

apply := method(fn, args, env,
  if (fn tag == "error",
    return fn)
  if (args tag == "error",
    return args)
  if (fn tag == "subr",
    return fn data call(args))
  if (fn tag == "expr",
    return progn(fn body, makeCons(pairlis(fn args, args), fn env)))
  makeError(printObj(fn) with(" is not function")))

subrCar := Object clone
subrCar call := method(args,
  safeCar(safeCar(args)))

subrCdr := Object clone
subrCdr call := method(args,
  safeCdr(safeCar(args)))

subrCons := Object clone
subrCons call := method(args,
  makeCons(safeCar(args), safeCar(safeCdr(args))))

addToEnv(makeSym("car"), makeSubr(subrCar), g_env)
addToEnv(makeSym("cdr"), makeSubr(subrCdr), g_env)
addToEnv(makeSym("cons"), makeSubr(subrCons), g_env)
addToEnv(makeSym("t"), makeSym("t"), g_env)

write("> ")
while (line := File standardInput readLine,
  writeln(printObj(eval(read(line) at(0), g_env)))
  write("> "))
