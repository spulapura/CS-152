open Ast
open Helper

exception TypeError 
exception UnificationError
exception UnimplementedError

(* [unify c0] solves [c0] (if possible), yielding a substitution. Raise UnificationError if constraints cannot be unified. *)
let rec unify (c0:constr) : subst = 
	if Constr.is_empty c0 then VarMap.empty else let (t1,t2) = Constr.choose c0 in  
	if typ_eq t1 t2 then let c = Constr.remove (t1,t2) c0 in unify c else
	match (t1, t2) with
	|TVar(x), _ -> let fv = ftvs t2 in if VarSet.mem x fv then raise UnificationError else let c1 = subst_constr c0 x t2 in VarMap.add x t2 (unify c1) 
	|_, TVar(x) -> let fv = ftvs t1 in if VarSet.mem x fv then raise UnificationError else let c1 = subst_constr c0 x t1 in VarMap.add x t1 (unify c1)
	|TArrow(a,b), TArrow(c,d) -> let c1 = Constr.add (a, c) c0 in let c = Constr.add (b,d) c1 in unify c
	|TPair(a,b), TPair(c,d) -> let c1 = Constr.add (a, c) c0 in let c = Constr.add (b, d) c1 in unify c
	|_,_ -> raise UnificationError


(* [check g e0] typechecks [e0] in the context [g] generating a type and a set of constraints. Raise TypeError if constraints cannot be generated. *)

let rec check (g: context) (e0: exp): typ * constr =
	match e0 with
	|Var(x)-> if VarMap.mem x g then (VarMap.find x g, Constr.empty) else let fv = next_tvar () in (fv, Constr.empty)
  	|App(e1, e2) -> let (t1, c1) = check g e1 in let (t2, c2) = check g e2 in let fv = next_tvar () 
  		in let c3 = Constr.add (t1, TArrow(t2, fv)) (Constr.union c1 c2) in (fv, c3)
  	|Lam(x, e) -> let fv = next_tvar () in let g1 = VarMap.add x fv g in let (t, c) = check g1 e in (TArrow(fv, t), c) 
  	|Let(x, e1, e2) -> let (t1, c1) = check g e1 in let g1 = (VarMap.add x t1 g) in let (t,c) = check g1 e2 in (t, Constr.union c c1) 
  	|Int(n) -> (TInt, Constr.empty)
  	|Plus(e1, e2) -> let (t1, c1) = check g e1 in let (t2, c2) = check g e2 in 
  		let c = Constr.add (t2, TInt) (Constr.add (t1, TInt) (Constr.union c1 c2)) in (TInt, c) 
  	|Times(e1, e2) -> let (t1, c1) = check g e1 in let (t2, c2) = check g e2 in 
  		let c = Constr.add (t2, TInt) (Constr.add (t1, TInt) (Constr.union c1 c2)) in (TInt, c)
  	|Minus(e1, e2) -> let (t1, c1) = check g e1 in let (t2, c2) = check g e2 in 
  		let c = Constr.add (t2, TInt) (Constr.add (t1, TInt) (Constr.union c1 c2)) in (TInt, c)
  	|Pair(e1, e2) -> let(t1, c1) = check g e1 in let (t2, c2) = check g e2 in 
  		let c = Constr.union c1 c2 in (TPair(t1, t2), c)
	|Fst(e) -> let (t1, c1) = check g e in let fv1 = next_tvar () in let fv2 = next_tvar () in 
		let c = Constr.add (t1, TPair(fv1, fv2)) c1 in (fv1, c)
  	|Snd(e) -> let (t1, c1) = check g e in let fv1 = next_tvar () in let fv2 = next_tvar () in 
		let c = Constr.add (t1, TPair(fv1, fv2)) c1 in (fv2, c)
  	|True -> (TBool, Constr.empty)
  	|False -> (TBool, Constr.empty)
  	|Eq(e1, e2) -> let (t1, c1) = check g e1 in let (t2, c2) = check g e2 in let c3 = Constr.union c1 c2 in 
  		let c = Constr.add (t1, t2) c3 in (TBool, c) 
  	|If(e1, e2, e3) -> let (t1, c1) = check g e1 in let (t2, c2) = check g e2 in let (t3, c3) = check g e3 in
  		let c4 = Constr.union (Constr.union c1 c2) c3 in let c = Constr.add (t1, TBool) (Constr.add (t2, t3) c4) in (t2, c) 
  	|Letrec(f, x, e1, e2) -> let fv = next_tvar () in let g1 = VarMap.add x fv g in let (t1, c1) = check g1 e1 in 
  		let g2 = VarMap.add f (TArrow(fv, t1)) g in let (t,c) = check g2 e2 in (t, Constr.union c1 c) 
    |_ -> raise TypeError


