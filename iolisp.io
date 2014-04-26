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
  cell cdr := d)

makeSubr := method(fn,
  makeLObj("subr", fn))

makeExpr := method(args, env,
  expr := LObj clone
  expr tag := "expr"
  expr args := safeCar(args)
  expr body := safeCdr(args)
  expr env := env)

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
    return list(makeError("noimpl"), ""))
  if (c == kQuote,
    return list(makeError("noimpl"), ""))
  return readAtom(str))

write("> ")
while (line := File standardInput readLine,
  writeln(read(line) at(0))
  write("> "))
