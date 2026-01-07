# Coq Tactics Cheatsheet

A reference guide for Coq tactics learned from Software Foundations Volume 1.

## Quick Reference - All Tactics

### Core Proof Tactics
- [`reflexivity`](#reflexivity) - finish the proof when goal is `e = e`
- [`simpl`](#simpl) - simplify computations in the goal
- [`simpl in H`](#tactics-with-in-h-variants) - simplify in a hypothesis
- [`intro` / `intros`](#intro--intros) - move hypotheses/variables from goal to context
- [`rewrite`](#rewrite) - use an equality to rewrite the goal
- [`rewrite ... in H`](#tactics-with-in-h-variants) - rewrite in a hypothesis
- [`destruct ... as ...`](#destruct) - case analysis on inductively defined types
- [`destruct ... eqn:...`](#destruct-on-compound-expressions) - case analysis with equation naming
- [`induction ... as ...`](#induction) - induction on inductively defined types

### Application and Reasoning
- [`apply`](#apply) - prove goal using a hypothesis, lemma, or constructor
- [`apply ... in H`](#apply) - apply to a hypothesis (forward reasoning)
- [`apply ... with ...`](#apply--with) - explicitly specify values for variables
- [`symmetry`](#symmetry) - change `t = u` into `u = t`
- [`symmetry in H`](#symmetry) - swap equality in a hypothesis
- [`transitivity`](#transitivity) - prove `x = z` via intermediate value `y`

### Constructor Properties
- [`injection ... as ...`](#injection) - reason by injectivity of constructors
- [`discriminate`](#discriminate) - reason by disjointness of constructors
- [`f_equal`](#f_equal) - change `f x = f y` into `x = y`

### Definitions and Substitution
- [`unfold`](#unfold) - replace a defined constant by its definition
- [`unfold ... in H`](#unfold) - unfold in a hypothesis
- [`replace`](#replace) - replace a subterm with another, generating a subgoal

### Intermediate Results
- [`assert (H: e)`](#assert) - introduce a local lemma
- [`generalize dependent`](#generalize-dependent) - move variable back to goal

### Search and Information
- [`Search`](#search) - find theorems in the environment
- [`Check`](#check) - display the type of an expression
- [`@`](#-at-symbol) - make implicit arguments explicit
- [`Arguments`](#arguments) - declare implicit arguments

### Special Commands
- [`Fail`](#fail) - assert that a command should fail
- [`Admitted`](#admitted) - accept theorem without proof
- [`Qed`](#qed) - complete and save proof

## [Basics](https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html) 

### `reflexivity`
**Description:** Proves that an expression is equal to itself. Automatically simplifies both sides before checking equality.

### `simpl`
**Description:** Simplifies expressions by performing computation steps (function applications, pattern matching, etc.).

### `intro` | `intros`
**Description:** Moves hypotheses/variables from the goal into the context. Can name multiple variables at once.


### `rewrite`
**Description:** Replaces one side of an equality with the other throughout the goal. Use `->` for left-to-right and `<-` for right-to-left.

**Example:**
```coq
Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m H.  (* H: n = m *)
  rewrite <- H.  (* Replace m with n |- n + n = n + n *)
  reflexivity.
Qed.
```

**With left-to-right:**
```coq
rewrite -> H.  (* or just: rewrite H. *)
```

**With right-to-left:**
```coq
rewrite <- H.
```

### `destruct`
**Description:** Performs case analysis on an expression, generating one subgoal for each constructor. Use `as` to name the resulting variables/hypotheses.

**Example:**
```coq
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.
  
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) reflexivity.
Qed.
```

**With equation naming:**
```coq
destruct n as [| n'] eqn:E.
(* E : n = 0  or  E : n = S n' *)
```

### `induction`
**Description:** Performs proof by induction on an expression. Similar to `destruct` but adds an induction hypothesis in the inductive case.

**Example:**
```coq
Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
Qed.
```

## Proof Structure

### Bullets and Braces
**Description:** Organize subgoals in a proof for readability. Can use `-`, `+`, `*` as bullets, or `{ }` for braces.


## Special Commands

### `Admitted`
**Description:** Accepts a theorem without proof (for incomplete exercises or axioms).


### `Qed`
**Description:** Completes and saves a proof, making it opaque (proof details hidden).


## [Induction](https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html)

### `replace`
**Description:** Replaces a specific subterm in the goal with another expression, generating an equality subgoal. More precise than `rewrite` when you want to control exactly which occurrence gets rewritten.

**Example:**
```coq
Theorem replace_example : forall n : nat,
  n + n = n * 2.
Proof.
  intros n.
  replace (n + n) with (n * 2).
  - reflexivity.
  - (* Must prove: n + n = n * 2 *)
    ring.
Qed.
```

**Syntax:**
```coq
replace (t) with (u).
(* Replaces all copies of expression t with u in the goal *)
(* Generates subgoal: t = u *)
```


## [Lists](https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html)

### `Search`
**Description:** Searches for theorems in the Coq environment. Useful for finding relevant lemmas and theorems when you can't remember their names.

**Examples:**
```coq
Search rev.
(* Displays all theorems involving rev *)

Search (_ + _ = _ + _).
(* Searches for theorems with pattern matching additions *)

Search (_ + _ = _ + _) inside Induction.
(* Restricts search to the Induction module *)

Search (?x + ?y = ?y + ?x).
(* Uses variables instead of wildcards for more precise search *)
(* Question mark indicates a search pattern variable *)
```

**Usage notes:**
- Use wildcards `_` to match any expression
- Use pattern variables `?x`, `?y` for more specific patterns
- Use `inside ModuleName` to restrict search scope


## [Poly](https://softwarefoundations.cis.upenn.edu/lf-current/Poly.html)

### `Arguments`
**Description:** Declares which arguments of a function or constructor should be implicit. Implicit arguments are automatically inferred by Coq and don't need to be explicitly provided.

**Example:**
```coq
Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X}.

(* Now we can write: *)
Definition mylist := cons 1 (cons 2 (cons 3 nil)).
(* Instead of: *)
Definition mylist' := cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
```

**Alternative syntax in definitions:** declare an argument to be implicit when defining the function itself, by surrounding it in curly braces instead of parens.
```coq
(* Declare implicit arguments directly in function definition *)
Fixpoint repeat {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat x count')
  end.
```

### `Check`
**Description:** Displays the type of an expression or term. Useful for understanding types and verifying definitions.

**Examples:**
```coq
Check nil : forall X : Type, list X.
Check cons : forall X : Type, X -> list X -> list X.
Check (cons 1 (cons 2 nil)) : list nat.

(* With @ to make implicit arguments explicit *)
Check @nil : forall X : Type, list X.
```

### `@` (At symbol)
**Description:** Prefix for function names to make all implicit arguments explicit. Forces you to provide arguments that would normally be inferred.

**Example:**
```coq
(* nil has implicit type argument X *)
Arguments nil {X}.

(* This would fail - Coq doesn't know which type *)
Fail Definition mynil := nil.

(* Using @ makes the implicit argument explicit *)
Check @nil : forall X : Type, list X.
Definition mynil := @nil nat.
```

**Usage:**
```coq
(* With implicit arguments *)
Definition list123 := cons 1 (cons 2 nil).

(* With @ to make explicit *)
Definition list123' := @cons nat 1 (@cons nat 2 (@nil nat)).
```

### `Fail`
**Description:** A qualifier that can prefix any command to assert that the command should fail. If the command succeeds, Coq reports an error. If it fails as expected, Coq continues processing. Useful for documentation and testing.

**Example:**
```coq
(* This definition should fail because Coq can't infer the type *)
Fail Definition mynil := nil.

(* After providing type information, it works *)
Definition mynil : list nat := nil.
```

**Usage notes:**
- Can be used with any Coq command
- Primarily used in examples and tests to demonstrate incorrect usage
- The error message from the failed command is displayed

### Functions as Data - Higher-Order Functions

**Description:** Coq treats functions as first-class citizens, allowing them to be passed as arguments to other functions, returned as results, and stored in data structures. Functions that manipulate other functions are called higher-order functions.

#### Higher-Order Function Basics

**Example - Simple higher-order function:**
```coq
Definition doit3times {X : Type} (f : X->X) (n : X) : X :=
  f (f (f n)).

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.
```

#### Common Higher-Order Functions

**`filter`** - Filters a list based on a predicate:
```coq
Fixpoint filter {X:Type} (test: X->bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
              else filter test t
  end.

Example test_filter1: filter even [1;2;3;4] = [2;4].
```

**`map`** - Applies a function to each element of a list:
```coq
Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
```

**`fold`** - Combines list elements using a binary operator:
```coq
Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Example fold_example1: fold mult [1;2;3;4] 1 = 24.
(* Computes: 1 * (2 * (3 * (4 * 1))) = 24 *)
```

#### Anonymous Functions

**Syntax:** `fun x => expression`

**Description:** Create functions "on the fly" without declaring them at the top level or giving them a name.

**Examples:**
```coq
(* Anonymous function that squares its input *)
Example test_anon: doit3times (fun n => n * n) 2 = 256.

(* Using anonymous function with filter *)
Example test_filter:
  filter (fun l => (length l) =? 1) [[1;2]; [3]; [4]] = [[3]; [4]].
```

#### Partial Application

**Description:** Functions can be applied to fewer arguments than they expect, returning a new function that expects the remaining arguments. All multi-argument functions in Coq work this way.

**Example:**
```coq
Definition plus3 := plus 3.
Check plus3 : nat -> nat.

Example test_plus3: plus3 4 = 7.
Proof. reflexivity. Qed.

(* plus has type nat -> nat -> nat, which is really nat -> (nat -> nat) *)
Check plus : nat -> nat -> nat.
```

#### Currying and Uncurrying

**Currying:** Converting from `X * Y -> Z` to `X -> Y -> Z`
**Uncurrying:** Converting from `X -> Y -> Z` to `X * Y -> Z`

**Example:**
```coq
Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

(* Using currying to enable partial application *)
Example test_map: map (plus 3) [2;0;2] = [5;3;5].
```


## [Tactics](https://softwarefoundations.cis.upenn.edu/lf-current/Tactics.html)

### `apply`
**Description:** Proves the goal by applying a hypothesis, lemma, or constructor. Works with both exact matches and conditional statements (implications). For implications, premises become new subgoals.

**Examples:**
```coq
(* Direct application *)
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
```

**Variant - `apply ... in H` (Forward reasoning):**
```coq
(* Apply L in H: if L is X -> Y and H matches X, replace H with Y *)
Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) -> m = n -> q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H.       (* H: n = m *)
  apply EQ in H.       (* H: p = q *)
  symmetry in H.       (* H: q = p *)
  apply H.
Qed.
```

**Usage notes:**
- Coq automatically instantiates universally quantified variables
- The conclusion must match the goal exactly (use `symmetry` if needed)
- Backward reasoning: proves goal by showing premises

### `apply ... with`
**Description:** Explicitly specifies values for variables that cannot be determined by pattern matching when using `apply`.

**Example:**
```coq
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
```

**Shorthand:** Can omit variable name if unambiguous: `apply trans_eq with [c;d]`

### `transitivity`
**Description:** Built-in tactic for proving equality transitivity. Equivalent to applying a transitivity lemma. Requires specifying the intermediate value.

**Example:**
```coq
Example trans_eq_example : forall (a b c d e f : nat),
  [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].  (* Create subgoals: [a;b]=[c;d] and [c;d]=[e;f] *)
  apply eq1.
  apply eq2.
Qed.
```

### `injection`
**Description:** Exploits the injectivity of constructors. If two values built with the same constructor are equal, their arguments must be equal. Generates equality hypotheses for the arguments.

**Examples:**
```coq
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
```

**Usage notes:**
- All constructors are injective
- Use `as` to name the generated equality hypotheses
- Can generate multiple equations from a single equality

### `discriminate`
**Description:** Uses the disjointness of constructors. If two values are built with different constructors, assuming they're equal leads to a contradiction, allowing us to prove anything (principle of explosion).

**Examples:**
```coq
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
```

**Usage notes:**
- Works with any equality between different constructors
- Immediately solves the goal from a contradictory hypothesis
- Embodies the principle of explosion

### `symmetry`
**Description:** Swaps the left and right sides of an equality in the goal or hypothesis.

**Examples:**
```coq
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
```

### `unfold`
**Description:** Replaces a defined name with its definition. Useful when `simpl` doesn't make progress or when you need to manually expand a definition.

**Example:**
```coq
Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.  (* Doesn't help *)
  unfold square.  (* Expands to: (n * m) * (n * m) = (n * n) * (m * m) *)
  (* Now we can proceed with multiplication properties *)
Qed.
```

**Variant:** `unfold ... in H` - Unfolds in a hypothesis

### `f_equal`
**Description:** Changes a goal of the form `f a1 ... an = f b1 ... bn` into subgoals `a1 = b1`, ..., `an = bn`. Automatically discharges trivial subgoals.

**Example:**
```coq
Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof.
  intros n m H.
  f_equal.  (* Changes goal from S n = S m to n = m *)
  apply H.
Qed.
```

### `generalize dependent`
**Description:** Moves a variable (and anything depending on it) from the context back into the goal as a universally quantified hypothesis. Essential for getting a sufficiently general induction hypothesis.

**Example:**
```coq
Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m.
  (* Both n and m are in context *)
  generalize dependent n.
  (* Now n is back in the goal: forall n, double n = double m -> n = m *)
  induction m as [| m' IHm'].
  (* IH is now general enough to be useful *)
Qed.
```

**When to use:**
- When induction on one variable requires another to remain quantified
- To strengthen an induction hypothesis
- When you've introduced variables too early

### Tactics with `in H` variants

**Description:** Most tactics have variants that operate on hypotheses instead of the goal.

**Examples:**
```coq
(* simpl in H *)
Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b -> (n =? m) = b.
Proof.
  intros n m b H.
  simpl in H.  (* Simplify the hypothesis *)
  apply H.
Qed.

(* rewrite in H *)
(* symmetry in H *)
(* unfold in H *)
(* apply L in H *)
```

### `destruct` on compound expressions

**Description:** `destruct` can perform case analysis on any expression, not just variables. Use `eqn:` to remember which case you're in.

**Example:**
```coq
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
```

**Critical:** Always use `eqn:` when destructing compound expressions - it records essential information for completing the proof.



