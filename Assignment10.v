Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import micromega.Lia.
Require Import Maps.
Require Import Imp.

(* Definitions from the Hoare Logic Chapter. *)

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.
Notation "P ->> Q" :=
  (assert_implies P Q)
    (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.
Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P)
  (at level 80) : hoare_spec_scope.

 Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st ->
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.


Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).
Notation "P [ X !-> a ]" := (assn_sub X a P)
                             (at level 10, X at next level).

(* Theorems for the different commands *)

(* Assignment *)
Theorem hoare_asgn : forall Q X a,
    {{ Q [X !-> a ] }} X ::= a {{ Q }}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ.
  assumption.
Qed.

(* Consequence *)
Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP.
  apply Himp.
  apply (Hhoare st st').
  assumption. assumption.
Qed.

(* Skip *)
Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.
Qed.

(* Sequencing *)
Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption.
Qed.

(* Conditionals *)
Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.
Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} TEST b THEN c1 ELSE c2 FI {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
      assumption.
      split. assumption.
      apply bexp_eval_true. assumption.
  - (* b is false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
      apply bexp_eval_false. assumption.
Qed.

(* Loops *)
Theorem hoare_while : forall P b c,
    {{fun st => P st /\ bassn b st}} c {{P}} ->
    {{P}} WHILE b DO c END {{fun st => P st /\ ~(bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction
     on He, because, in the "keep looping" case, its hypotheses
     talk about the whole loop instead of just c. *)
  remember (WHILE b DO c END)%imp as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)
    split. assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrue *)
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
    split. assumption. apply bexp_eval_true. assumption.
Qed.


(*********************************************************************************************************
** Exercises
**********************************************************************************************************)

(* Give proofs of the following theorems using the theorems given above. Read the chapter "Hoare Logic" in the
 Software Foundations book if you have problems understanding why the rules are formulated in the way given above. *)

(* Hints:
 - Use the "eapply" tactic liberally.
 - Use the "hoare_consequence_pre" and "hoare_consequence_post" theorems as "intermediate steps" if one of the other
   rules given above has the "wrong shape".
*) 

(* Exercise 1 *)
Theorem exercise1 : {{ fun st => st X = 20 /\ st Y = 30 }} SKIP {{ fun st => st Y = 30 /\ st X = 20 }}.
Proof.
  admit.
Admitted.

(* Exercise 2 *)
Theorem exercise2 : {{ fun st => st X = 20 /\ st Y = 30 }} SKIP {{ fun st => st Y = 30 }}.
Proof.
  admit.
Admitted.


(* Exercise 3 *)
Theorem exercise3 : {{ fun st => st X = 10 /\ st Y = 15 }} X ::= X + 1 ;; Y ::= Y + 1 {{ fun st => st X = 11 /\ st Y = 16 }}.
Proof.
  admit.
Admitted.

(* Exercise 4 *)
Theorem exercise4 : {{ fun st => True }} TEST (BLe X 20 : bexp) THEN X ::= 20 ELSE SKIP FI {{ fun st => 20 <= st X }}.
Proof.
  admit.
Admitted.

(* Exercise 5 *)
Definition prog5 : com :=
  WHILE ~ (X = 10) DO
    SKIP
  END.

Theorem exercise5 : {{ fun st => st X = 0 }} prog5 {{ fun st => st X = 10 }}.
Proof.
  admit.
Admitted.

(* Exercise 6 *)
Definition prog6 (n m : nat) : com :=
  X ::= n;;
  Y ::= m;;       
  Z ::= 0;;
  WHILE ~ (X = 0) DO
    Z ::= Z + Y;;
    X ::= X - 1
  END.

(* What does the program given above do? Based on your observation formulate a loop invariant that is preserved by the loop body. *)
Definition loopInvariant (n m : nat) : Assertion := fun st => True (* TODO *).


Theorem exercise6 : forall n m, {{fun st => True }} (prog6 n m) {{ fun st => st Z = n * m }}.
Proof.
  admit.
Admitted.


  
