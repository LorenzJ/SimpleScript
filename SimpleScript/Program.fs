open FParsec
open System

type Operator = Addition
              | Subtraction
              | Division
              | Multiplication
              | Equality
              | LessThan
              | LessOrEqual
              | GreaterThan
              | GreaterOrEqual
              | And
              | Or

type Value = Number of float
           | String of string
           | Bool   of bool
           | Array  of Value list
           | Object of (string * Value) list
           | ErrorValue
           | Unit
           | Function of string list * Expression
and Expression = Constant of Value
               | Variable of string
               | Call     of string * Expression list
               | BinOp    of Operator * Expression * Expression
               | ExprList of Expression list
               | Branch   of Expression * Expression * Expression option
               | Declaration of string * Expression
               | FuncDecl    of string * string list * Expression

type Parser<'a> = Parser<'a, unit>

let ws = spaces
let str x = pstring x .>> ws

let identifier =
    let firstChar c = c = '_' || isLetter c
    let others c = firstChar c || isDigit c
    many1Satisfy2 firstChar others .>> ws

let opp = OperatorPrecedenceParser<Expression, _, _>()
opp.AddOperator(InfixOperator("+", ws, 20, Associativity.Left, fun lhs rhs -> BinOp(Addition, lhs, rhs)))
opp.AddOperator(InfixOperator("-", ws, 20, Associativity.Left, fun lhs rhs -> BinOp(Subtraction, lhs, rhs)))
opp.AddOperator(InfixOperator("*", ws, 30, Associativity.Left, fun lhs rhs -> BinOp(Multiplication, lhs, rhs)))
opp.AddOperator(InfixOperator("/", ws, 30, Associativity.Left, fun lhs rhs -> BinOp(Division, lhs, rhs)))
opp.AddOperator(InfixOperator("==", ws, 10, Associativity.Left, fun lhs rhs -> BinOp(Equality, lhs, rhs)))
opp.AddOperator(InfixOperator("<", ws, 10, Associativity.Left, fun lhs rhs -> BinOp(LessThan, lhs, rhs)))
opp.AddOperator(InfixOperator("<=", ws, 10, Associativity.Left, fun lhs rhs -> BinOp(LessOrEqual, lhs, rhs)))
opp.AddOperator(InfixOperator(">", ws, 10, Associativity.Left, fun lhs rhs -> BinOp(GreaterThan, lhs, rhs)))
opp.AddOperator(InfixOperator(">=", ws, 10, Associativity.Left, fun lhs rhs -> BinOp(GreaterOrEqual, lhs, rhs)))
opp.AddOperator(InfixOperator("and", ws, 5, Associativity.Left, fun lhs rhs -> BinOp(And, lhs, rhs)))
opp.AddOperator(InfixOperator("or", ws, 6, Associativity.Left, fun lhs rhs -> BinOp(Or, lhs, rhs)))

let expr = opp.ExpressionParser
let exprList = sepEndBy expr (str ";") |> between (str "{") (str "}") |>> ExprList
let branch, branchRef = createParserForwardedToRef<Expression, _>()
do branchRef :=
    pipe3 (str "if" >>. expr)
          (expr)
          (opt(str "else" >>. choice[branch; expr]))
          (fun cond tr fl -> Branch(cond, tr, fl))
let variable = identifier .>> ws |>> Variable

let paramList = (sepEndBy identifier (str ";")) |> between (str "(") (str ")")
let funcDecl = 
    attempt(
        pipe3 (str "fn" >>. identifier)
              (paramList)
              (expr)
              (fun n p e -> FuncDecl(n, p, e)))
let funcProto =
    attempt(pipe2 (str "fn" >>. paramList)
          (expr)
          (fun p e -> Function(p, e) |> Constant))
let funcCall = attempt(identifier .>>. ((sepEndBy expr (str ";")) |> between (str "(") (str ")"))) |>> Call
let numberConstant = pfloat .>> ws |>> Number
let stringConstant = manySatisfy(fun c -> c <> '"') |> between (pstring "\"") (str "\"") |>> string |>> String
let boolConstant =
    choice[str "true"
           str "false"] |>> function
                            | "true" -> Bool(true)
                            | _ -> Bool(false)
let constant =
    choice[numberConstant
           stringConstant
           boolConstant] |>> Constant

let declaration = ((str "let " >>. identifier) .>>. (str "=" >>. expr)) |>> Declaration

opp.TermParser <-
    choice[branch
           funcDecl
           funcProto
           declaration
           funcCall
           variable
           constant
           exprList
           expr |> between (str "(") (str ")")]

let program:Parser<_> = ws >>. many(expr) |>> ExprList .>> eof

type VarMap = Map<string, Value>
let eval (x:Expression) =
    let printFunc value = 
        printf "%A" value
        Unit
    let convertToNumber (value: Value list) =
        match value.Head with
        | Number(n) -> Number(n)
        | String(s) -> Number(Convert.ToDouble(s))
        | Bool(b)   -> if b then Number(1.0) else Number(0.0)
        | _ -> ErrorValue
    let convertToString (value: Value list) =
        match value.Head with
        | Number(n) -> String(Convert.ToString(n))
        | Bool(b)   -> if b then String("true") else String("false")
        | String(s) -> String(s)
        | _ -> ErrorValue
    let inputFunc (value: Value list) =
        String(Console.ReadLine())
    let convertToUnit (value: Value list) = Unit
    let builtinFunctionMap = 
        Map([("Print", printFunc)
             ("Number", convertToNumber)
             ("String", convertToString)
             ("Input", inputFunc)
             ("Unit", convertToUnit)])
    let initialVariableMap = 
        VarMap([("void", Unit)
                ("pi", Number(Math.PI))
                ("e", Number(Math.E))])

    let addFunctionMap e varMap=
        let rec loop e (fnMap:VarMap) =
            match e with
            | ExprList(exprList) ->
                match exprList with
                | head :: tail ->
                    match head with
                    | FuncDecl(n, p, e) ->
                        loop (tail |> ExprList) (fnMap.Add(n, Function(p, e)))
                    | _ -> loop e fnMap
                | [] ->
                    fnMap
            | _ -> fnMap
        loop e varMap
    
    let finalVarMap = initialVariableMap |> addFunctionMap x
    let getFunc name (varMap:VarMap) = 
        let f = varMap.TryFind(name)
        match f with
        | Some(pe) ->
            match pe with
            | Function(p, e) -> pe
            | _ -> ErrorValue
        | None -> ErrorValue

    
    let doEval (e:Expression) (variableMap:VarMap) =
        let calc lhs rhs op =
            match lhs with
            | Number(l) ->
                match rhs with
                | Number(r) -> Number(op l r)
                | _ -> ErrorValue
            | _ -> ErrorValue
        let cmp lhs rhs op =
            match lhs with
            | Number(l) ->
                match rhs with
                | Number(r) -> Bool(op l r)
                | _ -> ErrorValue
            | _ -> ErrorValue
        let comb lhs rhs op =
            match lhs with
            | Bool(l) ->
                match rhs with
                | Bool(r) -> Bool(op l r)
                | _ -> ErrorValue
            | _ -> ErrorValue
        let add lhs rhs =
            match lhs with
            | Number(l) -> calc lhs rhs (+)
            | String(l) ->
                match rhs with
                | String(r) -> String(l + r)
                | _ -> ErrorValue
            | _ -> ErrorValue
        let sub lhs rhs = calc lhs rhs (-)
        let mul lhs rhs = calc lhs rhs (*)
        let div lhs rhs = calc lhs rhs (/)
        let equ lhs rhs = cmp lhs rhs (=)
        let lt  lhs rhs = cmp lhs rhs (<)
        let le  lhs rhs = cmp lhs rhs (<=)
        let gt  lhs rhs = cmp lhs rhs (>)
        let ge  lhs rhs = cmp lhs rhs (>=)
        let cand lhs rhs = comb lhs rhs (&&)
        let cor  lhs rhs = comb lhs rhs (||)

        let rec recEval (varMap:VarMap) (outerScope:VarMap) expr =
            match expr with
            | FuncDecl(_,_,_) -> Unit
            | Constant(c) -> c
            | Variable(v) -> 
                match (varMap.TryFind(v)) with
                | Some(value) -> value
                | None ->
                    match (outerScope.TryFind(v)) with
                    | Some(value) -> value
                    | None -> ErrorValue

            | Call(n, argList) ->
                let args = argList |> List.map(recEval varMap outerScope)
                let rec findInScope n scopeList =
                    match scopeList with
                    | head :: tail -> 
                        match getFunc n head with
                        | Function(p, e) -> 
                            let argMap = List.zip p args
                            recEval (VarMap(argMap)) outerScope e
                        | _ -> findInScope n tail
                    | [] -> 
                        let func = builtinFunctionMap.TryFind(n)
                        match func with
                        | Some(f) -> f args
                        | None -> ErrorValue 
                findInScope n [varMap; outerScope]
            | BinOp(op, lhs, rhs) ->
                let lhsv = recEval varMap outerScope lhs
                let rhsv = recEval varMap outerScope rhs
                match op with
                | Addition       -> add lhsv rhsv
                | Subtraction    -> sub lhsv rhsv
                | Division       -> div lhsv rhsv
                | Multiplication -> mul lhsv rhsv
                | Equality       -> equ lhsv rhsv
                | LessThan       -> lt  lhsv rhsv
                | LessOrEqual    -> le  lhsv rhsv
                | GreaterThan    -> gt  lhsv rhsv
                | GreaterOrEqual -> ge  lhsv rhsv
                | And            -> cand lhsv rhsv
                | Or             -> cor  lhsv rhsv

            | ExprList(el) ->
                let rec loop varMap exprList retValue =
                    match exprList with
                    | head :: tail ->
                        match head with
                        | Declaration(n, e) ->
                            let v = recEval varMap outerScope e
                            let newVarMap = varMap.Add(n, v)
                            loop newVarMap tail v
                        | _ -> loop varMap tail (recEval varMap outerScope head)
                            
                    | [] -> retValue
                loop varMap el Unit
            | Branch(c, t, f) ->
                let result = recEval varMap outerScope c
                match result with
                | Bool(b) ->
                    if b then
                        recEval varMap outerScope t
                    else
                        match f with
                        | Some(x) -> 
                            recEval varMap outerScope x
                        | None -> Unit
                | _ -> ErrorValue
            | Declaration(_, _) -> 
                printfn "Reaching declaration here should be impossible!"
                ErrorValue
        recEval variableMap variableMap e

    let entry = getFunc "main" finalVarMap
    match entry with
    | Function(n, e) ->
        doEval e finalVarMap
    | _ ->
        doEval x finalVarMap

let script = """
fn fact(x) if x == 0 1 else x * fact(x - 1)

fn min(lhs; rhs) if lhs < rhs lhs else rhs

fn max(lhs; rhs) if lhs > rhs lhs else rhs

fn recPow(a; x; i) if i == 0 a else recPow(a * x; x; i - 1)
fn pow(x; p) recPow(1; x; p)

fn main()
{
    let a = 2.0;
    Print(a);
    Print("My test script");
    Print(fact(9));
    let myBool = 5 == 5 or 3 == 3;
    Print(myBool);
    let myNumber = if a < 8.0 a else 0.0;
    let theResult =
    {
        let b = Number(Input());
        if b == 1337.0 5
        else if b < 0.0 "what"
        else fact(Number(b));
    };
    Print("The result is: ");
    Print(theResult);  
    Print(pow(5;3));
    Print(String(2) + String(3))


}
"""
[<EntryPoint>]
let main argv = 
    match run program script with
    | Success(result, _, _) -> printfn "%A" (eval result)
    | Failure(msg, _, _)    -> printfn "%s" msg
    Console.ReadKey true |> ignore
    0 // return an integer exit code
