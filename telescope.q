// Jose Cambronero (josepablocam@gmail.com)
// Simulates lexically scoped local variables by using partial function evaluation
// Limitations:
// 1 - Original function must be definable in q
//  for example: {a:a * 10} won't define a function in q, so cannot be
//  handed over to telescope (telescope isn't magic!)
// 2 - There can be no identical function definitions in a function handed
//  to telescope. This is an ugly limitation that I plan to fix, but for now
//  it allows me to exploit `value` to determine use/def of variables
// 3 - Any nested functions should be written so as to match the form
// when value is applied to it (i.e. avoid unnecessary spaces etc)
// This is annoying and I plan to fix this bit.


// Important constants
// function type
.tele.FUN_TYPE:type {};
// marker used to find line/col position of a function definition
.tele.MARKER:" .tele._MARKER_ "

// non-local variables used in function (i.e. use w/o def)
// args:
//  -x: result of applying value to function
.tele.nonlocals:{v where not null v:x 3}
// local variables defined in function
// args:
//  -x: result of applying value to function
.tele.locals:{x 2}
// formals parameters in function
// args:
//  -x: result of applying value to function
.tele.formals:{x 1}
// string representation of function
// args:
//  -x: result of applying value to function
.tele.strRep:{last x}
// functions defined in function (depth = 1)
// args:
//  -x: result of applying value to function
.tele.funs:{x where .tele.FUN_TYPE=type each x}
// all functions (closure)
.tele.allFuns:{raze (raze .tele.funs each value each)\[(),x]}
// remove formals from function signature
// args:
//  -x: string representation of function
.tele.remFormals:{
  $["["=first x;
   (1+first where 0=sums 0^("[]"!1 -1) s) _ s:trim x;
   x]
  }
// add formals to function signature (string representation)
// args:
//  -nms: symbol list of formal parameter names
//  -body: string representation of the body of the function
.tele.addFormals:{[nms; body] ("[", ";" sv string nms),"] ",body}
// create partial evaluation call for a function
// args:
//  -ctf: count of original formal parameters
//  -nls: symbol list of non-local variables
.tele.pEval:{[ctf;nls]
  $[count nls;
   ("[",";" sv string (ctf#`),nls),"]";
  ""]
   }
// sanitize a ssr replacement string
// replaces all reserved chars with explicit representation
// args:
//  -x: replacement string
.tele.sanitizePattern:{
  raze {$[y in key x;x y;y]}["*+[]"!("[*]";"[+]";"[[]";"[]]");] each x
  }

// List local variables in immediate scope of a given function definition
// args:
//  enclosing: string representation of enclosing function, (w/o {} or formals)
//  f: string representation of function for which we want to find in-scope vars
.tele.inScope:{[enclosing; f]
  // replace function definition with special marker and make into symbols
  marked:`$string parse ssr[enclosing;.tele.sanitizePattern f;.tele.MARKER];
  // flatten out parse tree of each command in function
  flat:(raze/) each marked;
  // line containining our function, anything after is not in scope
  line:first where (`$.tele.MARKER) in/:flat;
  upto:(line+1) sublist flat;
  // definitions in scope of function
  defs:(`:=upto)&(maxs each not nm)|all each nm:(`$.tele.MARKER)<>upto;
  // variables associated with definitions
  raze upto@'where each prev each defs
  }

// Recursive helper to extend function with local variables
.tele.extend0:{
  // function info
  funi:value x;
  // formal params used/defined
  fs:.tele.formals funi;
  // nonlocal variables used
  nls:.tele.nonlocals funi;
  // body of the function's string rep, w/o "{}"
  b:trim .tele.remFormals s:1_-1_ trim .tele.strRep funi;
  // nested functions for recursive resolution
  nfs:.tele.funs funi;
  // variables defined up to each function
  defs:.tele.inScope[b; ] each string nfs;
  // replacement info
  reps:`orig`scoped`nls!flip .tele.extend0 each nfs;
  // new string body with replaced functions
  nb:ssr/[b;.tele.sanitizePattern each reps`orig; reps`scoped];
  // remove any local variables defined at up to that point....
  nestednls:raze reps[`nls] except'defs;
  // need own nonlocals and those required by nested functions
  need:nls,nestednls;
  scoped:"{",.tele.addFormals[fs,need;nb],"}",.tele.pEval[count fs;need];
  (.tele.strRep funi;scoped;need)
 }

// Add "scoped" local variables to a function definition
// Uses parse/eval (former to create function, latter to partially eval where
// relevant)
.tele.scope:{eval parse (.tele.extend0 x) 1}

/
// Examples
// simple example, no global a
f:{a:100; g:{a * 2}; g[] + 4}
(.tele.scope f)[]~204

// simple example, global a shadowed by local
a:1000
f[]~2004
(.tele.scope f)[]~204

// simple example, global and local a, lexically scoped (i.e. bound at def time)
f:{g:{a * 2}; a:100; h:{a}; (g[];h[])}
f[]~2000 1000
(.tele.scope f)[]~2000 100

using namespaces, evaluates in normal q, but not expected result
f:{.test.a:100;g:{.test.a};.test.a:200;h:{.test.a + 2};(g[];h[])}
f[]~200 202
(.tele.scope f)[]~100 202

// multiple levels of nesting
f:{a:100; {h:{a}; a:200; g:{{a+2}[]};  (h[];g[])}[]}
f[]~1000 1002
(.tele.scope f)[]~100 202

// works as expected with local variables of other types
f:{x+y}
{f:{x * y}; {f[x;y]}[100;200]}[]~300
.tele.scope[{f:{x * y}; {f[x;y]}[100;200]}][]~20000
