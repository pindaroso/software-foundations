(* Tactic summary taken from Joseph Redmon's site at https://goo.gl/x9pZVb *)

Inductive even : nat -> Prop:=
 | even_O: even O
 | even_S: forall n, even n -> even (S(S n)).

Lemma two_is_even:
  even (S (S O)).
Proof.
  constructor.
  constructor.
Qed.

Lemma modus_ponens:
  forall p q : Prop, (p -> q) -> p -> q.
Proof.
  intros. apply H. apply H0.
Qed.

Lemma modus_ponens':
  forall p q : Prop, (p -> q) -> p -> q.
Proof.
  intros. apply H. assumption.
Qed.

Lemma modus_ponens'':
  forall p q : Prop, (p -> q) -> p -> q.
Proof.
  intros.
  apply H in H0.
  assumption.
Qed.

Inductive bool: Set :=
  | true
  | false.

Lemma equality_commutes:
  forall (a: bool) (b: bool), a = b -> b = a.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma equality_of_functions_commutes:
  forall (f: bool->bool) x y,
    (f x) = (f y) -> (f y) = (f x).
Proof.
  intros. rewrite -> H. reflexivity.
Qed.

Lemma equality_of_functions_transits:
  forall (f: bool->bool) x y z,
    (f x) = (f y) ->
    (f y) = (f z) ->
    (f x) = (f z).
Proof.
  intros. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma equality_of_functions_transits':
  forall (f: bool->bool) x y z,
    (f x) = (f y) ->
    (f y) = (f z) ->
    (f x) = (f z).
Proof.
  intros. rewrite H0 in H. assumption.
Qed.

Fixpoint add (a: nat) (b: nat) : nat :=
  match a with
    | O => b
    | S x => S (add x b)
  end.

Lemma zero_plus_n_equals_n:
  forall n, (add O n) = n.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma xyz:
  forall (f: bool->bool) x y z,
    x  = y -> y = z -> f x = f z.
Proof.
  intros.
  cut (x = z).
  - intro. subst. reflexivity.
  - rewrite H. rewrite H0. reflexivity.
Qed.

Definition inc (n : nat) : nat := n + 1.

Lemma foo_defn : forall n, inc n = S n.
Proof.
  intros.
  unfold inc.
  rewrite <- plus_n_Sm.
  rewrite <- plus_n_O.
  reflexivity.
Qed.

Definition not (b: bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Lemma not_not_x_equals_x:
  forall b, not (not b) = b.
Proof.
  intro. destruct b.
  - reflexivity.
  - simpl. reflexivity.
Qed.
