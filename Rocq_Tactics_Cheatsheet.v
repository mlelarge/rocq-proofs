Require Import Arith.
Require Import List.  (* Import standard library lists *)
Import ListNotations.  (* Import the [] and :: notations *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m H.  (* H: n = m *)
  rewrite <- H.  (* Replace m with n |- n + n = n + n *)
  reflexivity.
Qed.

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) reflexivity.
Qed.

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem replace_example : forall n : nat,
  n + n = n * 2.
Proof.
  intros n.
  replace (n + n) with (n * 2).
  - reflexivity.
  - (* Must prove: n + n = n * 2 *)
    ring. 
Qed.

Module mylist.

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X}.

(* Now we can write: *)
Definition mylist := cons 1 (cons 2 (cons 3 nil)).
(* Instead of: 
Definition mylist' := cons nat 1 (cons nat 2 (cons nat 3 (nil nat))). *)

(* This definition should fail because Coq can't infer the type *)
Fail Definition mynil := nil.

(* After providing type information, it works *)
Definition mynil : list nat := nil.
End mylist.

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).

Definition doit3times {X : Type} (f : X->X) (n : X) : X :=
  f (f (f n)).

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Fixpoint filter {X:Type} (test: X->bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
              else filter test t
  end.

(* Define even predicate *)
Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Example fold_example1: fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

(* Anonymous function that squares its input *)
Example test_anon: doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

(* Using anonymous function with filter *)
Example test_filter:
  filter (fun l => (length l) =? 1) [[1;2]; [3]; [4]] = [[3]; [4]].
Proof. reflexivity. Qed.

Definition plus3 := plus 3.
Check plus3 : nat -> nat.

Example test_plus3: plus3 4 = 7.
Proof. reflexivity. Qed.

(* plus has type nat -> nat -> nat, which is really nat -> (nat -> nat) *)
Check plus : nat -> nat -> nat.

(* Using currying to enable partial application *)
Example test_map: map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Theorem silly1 : forall (n m : nat), n = m -> n = m.
Proof.
  intros n m eq.
  apply eq.  (* Goal matches hypothesis exactly *)
Qed.

(* With conditional hypotheses *)
Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.  (* Creates subgoal: n = m *)
  apply eq1.  (* Proves the subgoal *)
Qed.

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) -> m = n -> q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H.       (* H: n = m *)
  apply EQ in H.       (* H: p = q *)
  symmetry in H.       (* H: q = p *)
  apply H.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite eq1. rewrite eq2. reflexivity.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
  [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).  (* Specify the middle value *)
  apply eq1. apply eq2.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
  [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].  (* Create subgoals: [a;b]=[c;d] and [c;d]=[e;f] *)
  apply eq1.
  apply eq2.
Qed.

(* Simple case *)
Theorem S_injective : forall (n m : nat), S n = S m -> n = m.
Proof.
  intros n m H.
  injection H as Hnm.  (* Generates hypothesis: n = m *)
  apply Hnm.
Qed.

(* Multiple equalities *)
Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] -> n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.  (* H1: n = o, H2: m = o *)
  rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem discriminate_ex1 : forall (n m : nat),
  false = true -> n = m.
Proof.
  intros n m contra.
  discriminate contra.  (* Contradiction: false ≠ true *)
Qed.

Theorem discriminate_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra.
  discriminate contra.  (* Contradiction: S n ≠ O *)
Qed.

(* In goal *)
Theorem silly3 : forall (n m : nat), n = m -> m = n.
Proof.
  intros n m H.
  symmetry.  (* Changes goal from m = n to n = m *)
  apply H.
Qed.

(* In hypothesis *)
Theorem example : forall (n m : nat), m = n -> n = m.
Proof.
  intros n m H.
  symmetry in H.  (* Changes H from m = n to n = m *)
  apply H.
Qed.

Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.  (* Doesn't help *)
  unfold square.  (* Expands to: (n * m) * (n * m) = (n * n) * (m * m) *)
  (* Now we can proceed with multiplication properties *)
  ring.
Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof.
  intros n m H.
  f_equal.  (* Changes goal from S n = S m to n = m *)
  apply H.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m.
  (* Both n and m are in context *)
  generalize dependent n.
  (* Now n is back in the goal: forall n, double n = double m -> n = m *)
  induction m as [| m' IHm'].
  (* IH is now general enough to be useful *)
Admitted.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat), sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.  (* Case analysis on expression *)
  - reflexivity.  (* E1: n =? 3 = true *)
  - destruct (n =? 5) eqn:E2.
    + reflexivity.  (* E2: n =? 5 = true *)
    + reflexivity.  (* E2: n =? 5 = false *)
Qed.