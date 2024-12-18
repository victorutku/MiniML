(* Q0  : Get familiar with the external syntax of MiniML *)
let parse_tests : (string * (string, exp) either) list = [
    (* Provide your tests for the parser *)
  ("1;", Right (Int 1))
]


let free_vars_tests : (exp * name list) list = [
  (Int 10, []);
  ((Let ([Val (Bool true, "x")],
         Let ([Val (Int 4, "y")], Primop (Plus, [Var "x"; Int 5])))),["y"]); 
  
]

(* Q1  : Find the free variables in an expression *)
let rec free_vars (e : exp) : name list = 
  match e with
  |Var x -> [x] 
  |If(e1,e2,e3) -> (union (free_vars e1)  (union (free_vars e2)  (free_vars e3))) 
  |Primop(op,exp_list)->List.fold_right (fun e1 -> union (free_vars e1)) exp_list []
  |Let([Val(e1,x)],e2)-> union (delete [x] (free_vars e2)) (free_vars e1)
  |Let([ByName(e1,x)],e2)-> union (delete [x] (free_vars e2)) (free_vars e1)
  |Let([Valtuple(e1,l)],e2) -> union(delete l (free_vars e2)) (free_vars e1)
  |Fn(n,_,e1) -> delete [n] (free_vars e1)
  |Rec(n,_,e1) -> delete [n] (free_vars e1)
  |Apply(e1,e2) -> union (free_vars e1) (free_vars e2)
  | _ -> [] 
         
         

let unused_vars_tests : (exp * name list) list = [ 
  ((Let ([Val (Bool true, "x")],
         Let ([Val (Int 4, "y")], Primop (Plus, [Var "x"; Int 5])))),["y"]);
  ((Let ([Val (Int 3, "x")],
         Let ([Val (Int 4, "x")], Primop (Plus, [Var "x"; Var "x"])))),["x"]);
  ((Fn ("x", None, Int 5)),["x"]);
  ((Fn ("x", None, Fn ("y", None, Primop (Plus, [Var "x"; Int 5])))),["y"]);
  ((If (Primop (Equals, [Var "x"; Int 5]), Let ([Val (Int 3, "x")], Int 4),
        Primop (Equals, [Var "y"; Int 6]))),["x"]);
  ((Let ([Val (Int 3, "x")],
         Let ([Valtuple (Tuple [Var "x"; Int 2], ["y1"; "y2"])],
              Primop (Plus, [Var "x"; Var "y1"])))),["y2"]);
  ((Let
      ([Val (Rec ("test", TArrow (TInt, TInt), Fn ("x", Some TInt, Int 3)),
             "test")],
       Int 4)),["test";"x"]);
  ((Let
      ([Val
          (Let ([Val (Int 10, "ten")],
                Anno (Fn ("y", None, Var "ten"), TArrow (TInt, TInt))),
           "f")],
       Apply (Var "f", Int 55))),[""]);
  ((Let ([Val (Bool true, "x")],
         Let ([Val (Int 1, "x")], Primop (Plus, [Var "x"; Int 5])))),["x"]);
  ((Let ([ByName (Int 3, "x")], Primop (Plus, [Var "x"; Int 1]))),[""]); 
]




(* Q2  : Check variables are in use *)
let rec unused_vars (e : exp) : name list = match e with
  |Let(ds,e2)-> (match ds with
      |Val(e1,n)::decs -> 
          if member n (free_vars e2) || member n (free_vars (Let(decs,e2)))
          then (unused_vars e2)
          else union [n] (unused_vars e1) 
      |Valtuple(e1,n)::decs -> 
          let a =List.filter(fun n1 ->  not(member n1 (free_vars e2))) n in
          if(a = [])
          then unused_vars (Let(decs,e2))
          else  union a (unused_vars e1)
      |ByName(e1,n)::decs -> 
          if member n (free_vars e2) then unused_vars e2 
          else union [n] (unused_vars e1)
      |_ ->[] )
  |Fn(n,t,e1) -> if member n (free_vars e1) then (unused_vars e1) else union [n]  (unused_vars e1)
  |Rec(n,t,e1)->  if member n (free_vars e1) then (unused_vars e1) else union [n] (unused_vars e1) 
  |_ -> []
                                                  


let subst_tests : (((exp * name) * exp) * exp) list = [
  
]

(* Q3  : Substitute a variable *)
let rec subst ((e', x) : exp * name) (e : exp) : exp =
  match e with
  | Var y ->
      if x = y then
        e'
      else
        Var y

  | Int _ | Bool _ -> e
  | Primop (po, es) -> Primop (po, List.map (subst (e', x)) es)
  | If (e1, e2, e3) -> If (subst (e', x) e1, subst (e', x) e2, subst (e', x) e3)
  | Tuple es -> Tuple (List.map (subst (e', x)) es)
  | Anno (e, t) -> Anno (subst (e', x) e, t)

  | Let (ds, e2) ->(match ds with
      |Val(e1,n):: decs->
          let e1' = subst (e',x) e1 in 
          if x = n then 
            Let (Val(e1', n)::decs, e2) 
          else 
          if member n (free_vars e') then 
            let y'  = fresh_var n in 
            let rename = subst (Var y', n) (Let(Val(e1, y')::decs, e2))in
            subst(e',x) rename
          else 
            subst (e',x) (Let (Val(e1', n)::decs,e2))
      |ByName(e1,n)::decs ->
          let e1' = subst (e',x) e1 in 
          if x = n then 
            Let (ByName(e1', n)::decs, e2) 
          else 
          if member n (free_vars e') then 
            let y'  = fresh_var n in 
            let rename = subst (Var y', n) (Let(ByName(e1, y')::decs, e2))in
            subst(e',x) rename
          else 
            subst (e',x) (Let (ByName(e1', n)::decs,e2))
      |Valtuple(e1,n_list )::decs -> 
          subst(e',x) (Let(Valtuple(e1,n_list)::decs,e2))
      |_-> raise (Stuck" not decs"))
          
          
  | Apply (e1, e2) -> Apply(subst(e',x)e1,subst(e',x)e2)
  | Fn (y, t, e) -> if x=y 
      then Fn(y,t,e) 
      else if member y (free_vars e') 
      then Fn((fresh_var y),t,subst(e',x)e) 
      else Fn(y,t,subst(e',x)e)
  | Rec (y, t, e) -> Rec(y,t,subst(e',x)e)


let eval_tests : (exp * exp) list = [
  (Primop(Or,[Bool true ; Bool false]),Bool true)
]

(* Q4  : Evaluate an expression in big-step *)
let rec eval : exp -> exp =
  (* do not change the code from here *)
  let bigstep_depth = ref 0 in
  fun e ->
    if !debug >= 1 then
      print_endline
        (String.make (!bigstep_depth) ' '
         ^ "eval (" ^ Print.exp_to_string e ^ ")\n");
    incr bigstep_depth;
  (* to here *)
    let result =
      match e with
      | Int _ | Bool _ -> e
      | Tuple es -> Tuple (List.map eval es)
      | If (e1, e2, e3) ->
          begin match eval e1 with
            | Bool b ->
                if b then
                  eval e2
                else
                  eval e3
            | _ -> stuck "Condition for if expression should be of the type bool"
          end
      | Anno (e, _) -> eval e     (* types are ignored in evaluation *)
      | Var x -> stuck ("Free variable \"" ^ x ^ "\" during evaluation")

      | Fn (x, t, e) -> Fn(x,t, e)
      | Apply (e1, e2) ->
          let v2 = eval e2 in
          (match e1 with
           |Fn(x,t,e3)-> Fn(x,t,subst(v2,x)e3)
           |_ -> raise (Stuck" not a function")) 
      | Rec (f, t, e) -> Rec(f,t,subst(e,f)e)

      | Primop (And, es) -> (match es with
          |[Bool true;Bool true] -> Bool true
          |[Bool false ;Bool false] -> Bool false
          |[Bool true; Bool false] | [Bool false; Bool true] -> Bool false
          | _ -> raise (Stuck " should be bool"))
      | Primop (Or, es) -> (match es with
          |[Bool true; Bool true] -> Bool true
          |[Bool false ; Bool false] -> Bool false
          |[Bool true; Bool false]|[Bool false ; Bool true] -> Bool true
          | _ -> raise (Stuck" not a boolean"))
      | Primop (op, es) ->
          let vs = List.map eval es in
          begin match eval_op op vs with
            | None -> stuck "Bad arguments to primitive operation"
            | Some v -> v
          end

      | Let (ds, e) -> match ds with
        |Val(e1,n):: decs-> 
            let v1= eval e1 in 
            subst(v1,n)(Let(decs,e))
        |Valtuple(e1,l)::decs ->
            let Tuple(v_lists) = eval e1 in
            let subslist = List.map2 (fun v n -> (subst(v,n)(Let(decs,e)))) v_lists l in
            Tuple (subslist ) 
        |ByName(e1,n)::decs-> subst(e1,n) (Let(decs,e))
        |_ -> eval e
    in
  (* do not change the code from here *)
    decr bigstep_depth;
    if !debug >= 1 then
      print_endline
        (String.make (!bigstep_depth) ' '
         ^ "result of eval (" ^ Print.exp_to_string e ^ ") = "
         ^ Print.exp_to_string result ^ "\n");
  (* to here *)
    result





let unify_tests : ((typ * typ) * unit) list = [
]

(* find the next function for Q5 *)
(* Q6  : Unify two types *)

                    
let rec unify (ty1 : typ) (ty2 : typ) : unit = 
  if ty1= ty2 then () 
  else match ty1, ty2 with
    |TInt ,TBool -> raise(TypeError " type dosn't match")
    |TInt, TVar x | TVar x , TInt -> x:= Some TInt
    |TBool, TVar x | TVar x ,TBool -> x:=Some TBool
    |TVar x ,TArrow(a,b) | TArrow(a,b), TVar x -> x:=Some (TArrow(a,b))
    |TProduct l ,TVar x | TVar x , TProduct l -> x:=Some  (TProduct l) 
    |TArrow(a,b) ,TArrow(c,d) -> 
        unify a c ;
        unify b d
    |TProduct l , TProduct l2 -> List.iter2 unify l l2
    |_,_ -> raise  (TypeError"No such type exists")
            

let infer_tests : ((context * exp) * typ) list = [
  ((Ctx[("",TBool)],Tuple[Int 1;Bool true]),TProduct[TInt;TBool])
]

(* Q5  : Type an expression *)
(* Q7* : Implement the argument type inference
         For this question, move this function below the "unify". *) 
let rec infer (ctx : context) (e : exp) : typ = match e with
  |Int _ -> TInt
  |Bool _ -> TBool
  |Anno (e1,t) -> infer ctx e1
  |Var n -> if (ctx =Ctx []) then raise (TypeError"error")
      else
        ctx_lookup ctx n 
  |Primop(op,exp_list) -> 
      let types = List.map( infer ctx) exp_list in 
      if((op = Plus||op = Minus||op=Times||op=Div) && types=[TInt;TInt]) then TInt
      else if( op= Negate && types =[TInt]) then TInt
      else if( types = [TInt ; TBool] || types =[TBool ;TInt]) then raise(TypeError"not valid") 
      else TBool 
  
  |If(e1,e2,e3)->
      (match e1 with 
       |Bool _ -> 
           let t1= infer ctx e2 in
           let t2 = infer ctx e3 in
           let uni = unify t1 t2 in
           if (uni =())then t1
           else raise (TypeError" e2 and e3 should have the same type")
       |_ -> raise (TypeError
                      " first expression in a if statement should be bool"))
  |Fn(n,t,e)-> (match t with
      |None -> let tv = fresh_tvar() in 
          infer (extend ctx (n,tv)) e
      |Some v ->
          let t2 = infer (extend ctx (n,v)) e in
          TArrow(v,t2))
  |Tuple(args) -> let t1 = List.map (infer ctx) args in
      TProduct t1
  |Rec(n,t,e)-> infer (extend ctx (n,t)) e
  |Apply(e1,e2)-> (match (infer ctx e1) with
      |TArrow(t1,t3) ->
          let t2 = infer ctx e2 in
          let uni = unify t1 t2 in
          if (uni =()) then t3
          else raise (TypeError "input for e1 should be type of e2")
      | _ -> raise(TypeError"first expression should be a fucntion"))

        

  |Let(decs,e2) ->
      (match decs with
       |Val(e1,n):: decs' ->  
           let t1 =infer ctx e1 in 
           let ctx1 = extend ctx (n,t1) in
           let types_rest = List.map (fun (Val(e,n)) ->(n,infer ctx1 e)) decs' in
           if(decs'=[]) then infer ctx1 e2 else
             infer (extend_list (ctx1) types_rest)  e2 
       |ByName(e1,n)::decs'->
           let t1 = infer ctx e1 in
           infer (extend ctx (n,t1)) e2
       |Valtuple(e1,list)::decs' -> 
           let t1 = infer ctx e1 in
           let ctx_list = List.map (fun (n:name) -> (n,t1)) list in
           infer (extend_list ctx ctx_list) e2
       |_ -> raise (TypeError"No such type exists"))
  


(* Now you can play with the language that you've implemented! *)
let execute (s: string) : unit =
  match P.parse s with
  | Left s -> print_endline ("parsing failed: " ^ s)
  | Right e ->
      try
       (* first we type check the program *)
        ignore (infer (Ctx []) e);
        let result = eval e in
        print_endline ("program is evaluated to: " ^ Print.exp_to_string result)
      with
      | NotImplemented -> print_endline "code is not fully implemented"
      | Stuck s -> print_endline ("evaluation got stuck: " ^ s)
      | NotFound -> print_endline "variable lookup failed"
      | TypeError s -> print_endline ("type error: " ^ s)
      | e -> print_endline ("unknown failure: " ^ Printexc.to_string e)


(************************************************************
 *             Do not change these functions.               *
 *               They are needed for tests.                 *
 ************************************************************)
let list_to_string el_to_string l : string =
  List.fold_left
    begin fun acc el ->
      if acc = "" then
        el_to_string el
      else
        acc ^ "; " ^ el_to_string el
    end
    ""
    l
  |> fun str -> "[" ^ str ^ "]"

let run_test name f ts stringify : unit =
  List.iteri
    begin fun idx (input, expected_output) ->
      try
        let output = f input in
        if output <> expected_output then
          begin
            print_string (name ^ " test #" ^ string_of_int idx ^ " failed\n");
            print_string (stringify output ^ " <> " ^ stringify expected_output)
          end
      with
      | exn ->
          print_string (name ^ " test #" ^ string_of_int idx ^ " raised an exception:\n");
          print_string (Printexc.to_string exn)
    end
    ts

let run_free_vars_tests () : unit =
  run_test "free_vars" free_vars free_vars_tests (list_to_string (fun x -> x))

let run_unused_vars_tests () : unit =
  run_test "unused_vars" unused_vars unused_vars_tests (list_to_string (fun x -> x))

let run_subst_tests () : unit =
  run_test "subst" (fun (s, e) -> subst s e) subst_tests Print.exp_to_string

let run_eval_tests () : unit =
  run_test "eval" eval eval_tests Print.exp_to_string

let run_infer_tests () : unit =
  run_test "infer" (fun (ctx, e) -> infer ctx e) infer_tests Print.typ_to_string

let run_unify_tests () : unit =
  run_test "unify" (fun (ty1, ty2) -> unify ty1 ty2) unify_tests (fun () -> "()")

let run_all_tests () : unit =
  run_free_vars_tests ();
  run_unused_vars_tests ();
  run_subst_tests ();
  run_eval_tests ();
  run_infer_tests ();
  run_unify_tests ()
