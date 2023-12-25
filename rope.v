Require Import Coq.Strings.String.
Require Import Ascii.

Local Open Scope nat_scope.

Inductive Rope :=
| Leaf : string -> nat -> Rope
| Node : Rope -> nat -> Rope -> Rope.

Definition mkRope (s : string) : Rope :=
    Leaf s (String.length s).

Fixpoint len (r : Rope) : nat :=
    match r with
    | Leaf _ l => l
    | Node l _ r => len l + len r
    end.

Fixpoint index (r : Rope) (i : nat) : ascii :=
    match r with
    | Leaf s _ => match String.get i s with
                  | Some c => c
                    | None => " " (* dummy *)
                    end
    | Node l w r =>
        if Nat.ltb i w then
            index l i
        else
            index r (i - w)
    end.
    
Definition concat (l r : Rope) : Rope :=
    let w := len l in
    Node l w r.

Fixpoint splitAt (s : string) (i : nat) : string * string :=
    match i with
    | O => (""%string, s)
    | S i => match String.get 0 s with
             | Some c => let (l, r) := splitAt (String.substring 1 (String.length s - 1) s) i in
                         (String c l, r)
             | None => (""%string, s)
             end
    end.

Fixpoint split (r : Rope) (i : nat) : Rope * Rope :=
    match r with
    | Leaf s _ => let (l, r) := splitAt s i in
                  (Leaf l (String.length l), Leaf r (String.length r))
    | Node l w r =>
        if Nat.ltb i w then
            let (ll, lr) := split l i in
            (ll, concat lr r)
        else
            let (rl, rr) := split r (i - w) in
            (concat l rl, rr)
    end.

Definition insert (r : Rope) (i : nat) (s : string) : Rope :=
    let (l, r) := split r i in
    concat l (concat (Leaf s (String.length s)) r).

Definition delete (r : Rope) (i j : nat) : Rope :=
    let (l, r) := split r i in
    let (_, r) := split r (j - i) in
    concat l r.


Fixpoint collect (r : Rope) : string :=
    match r with
    | Leaf s _ => s
    | Node l _ r => collect l ++ collect r
    end.

Fixpoint balance (r : Rope) : Rope :=
    match r with
    | Leaf s l =>
        if Nat.ltb l 8 then
            r
        else
            let (l, r) := split r (Nat.div l 2) in
            Node l (len l) r
    | Node l w r =>
        let l := balance l in
        let r := balance r in
        Node l (len l) r
    end.

Theorem insert_delete : forall (r : Rope) (i j : nat) (s : string),
    collect (delete (insert r i s) i (i + String.length s)) = collect r.



Compute (collect (mkRope "Hello, world!")).
Compute (collect (insert (mkRope "Hello, world!") 3 " cruel")).
Compute (collect (delete (mkRope "Hello, world!") 5 11)).
Compute (index (mkRope "Hello, world!") 5).
Compute (collect (fst (split (mkRope "Hello, world!") 5))).
Compute (collect (snd (split (mkRope "Hello, world!") 5))).
Compute (collect (balance (mkRope "Hello, world!"))).
Compute (collect (balance (insert (mkRope "Hello, world!") 3 " cruel"))).
Compute (collect (balance (delete (mkRope "Hello, world!") 5 11))).

