Require Import Utf8.

Section Noniterability_of_induction.

Definition till (n : nat) (P : nat → Prop) := ∀ k, k<n → P k.
Definition prime (P : nat → Prop) (n : nat) := till n P → P n.
Definition univ (P: nat → Prop) := ∀ n, P n.
Notation "P '" := (prime P) (at level 1).

Print "<". Print "≤".
(* We see that ≤ is in fact basic relation in Coq's system
   (least reflexive S-closed on the right)
   and then < is defined from ≤ adding another S on the left.

   For this induction we need the von Neumann's order (∈)
   so we have to prove the equivalence of that with Coq's
   definitions: first for ≤, and then for <. *)

Theorem less_equal: ∀ m n, m ≤ S n → m ≤ n ∨ m = S n.
Proof.
  intros m n hyp. inversion hyp as [eql|n' less' n'j].
  - right. reflexivity.
  - left. assumption.
Qed.

Theorem less_succ: ∀ m n, m < S n → m < n ∨ m = n.
Proof.
  unfold "<". intros m n hyp. apply less_equal in hyp.
  destruct hyp as [first|second].
  - left. assumption.
  - right. injection second as [=eql]. assumption.
Qed.

Theorem strong_induction: ∀ P, univ P ' → univ P.
Proof.
  unfold univ. intros P hyp n. apply hyp.
  induction n as [|n IH].
  - unfold till. intros k contra. inversion contra.
  - unfold till. intros k less.
    apply less_succ in less as [less|eql].
    * apply IH. assumption.
    * subst. apply hyp. assumption.
Qed.

Theorem Šika1: ∀ P n, P ' ' n ↔ P ' n.
Proof.
  intros P n. split.
  - intros hyp till_n. apply hyp.
    + intros k less till_k. apply till_n. assumption.
    + assumption.
  - intros hyp till_n' till_n. apply hyp. assumption.
Qed.

End Noniterability_of_induction.


Section Geometry_Converses.

Variable (S : Set) (F G : S → Prop).

Definition exist (F : S → Prop) := ∃ x, F x.
Definition unique (G : S → Prop) := ∀ x y, G x ∧ G y → x = y.

Theorem Šika2: (∀ x, F x → G x) ∧ exist F ∧ unique G →
                   ∀ x, F x ↔ G x.
(* If every F is a G, and there are ≥1 Fs, and there are ≤1 Gs,
   then every G is an F too. 
   In fact we can generalize 1→n, although it becomes even more
   convoluted to express that using just logic:
   if F ⇒ G and #F ≥ n ≥ #G, then F ⇔ G.
   But ONLY FOR FINITE n: if F ⇒ G and #F ≥ ℵ₀ ≥ #G
   then not necessarily F ⇔ G.
   (Hilbert's hotel: for example, F x :⇔ x > 2, G x :⇔ x > 1) *)
Proof.
  intros (onedirection & least1F & most1G) x. split.
  - apply onedirection.
  - intros Gx. destruct least1F as (x0 & Fx0).
    replace x with x0.
    + assumption.
    + apply most1G. split.
      * apply onedirection. assumption.
      * assumption.
Qed.
(* The whole mystery comes solely from the clumsiness of
   first order logic to express counting quantifiers. *)

End Geometry_Converses.


(* Require Import Classical_Prop. *)

Section Equality_Characterization.

Variable X : Set.

Definition reflexive (J : X → X → Prop) := ∀ x, J x x.
(* Leibniz property can be expressed relationally or functionally
   - but they aren't equivalent, and don't give the same results!
   (maybe codomain of f could be differently set up, or maybe J
   itself could be expressed functionally, but I don't know how. *)
Definition fLeibniz (J : X → X → Prop) :=
  ∀ (x y : X) (f : X → X), J x y → J (f x) (f y).
Definition rLeibniz (J : X → X → Prop) :=
  ∀ (x y : X) (P : X → Prop), J x y → P x → P y.
Definition RL (J : X → X → Prop) := reflexive J ∧ rLeibniz J.
Definition trueEquality (x y : X) := x = y.

Example rlj: RL trueEquality.
Proof. split.
  - intros x. reflexivity.
  - intros x y f xy. unfold trueEquality in xy.
    subst. intros hyp. assumption.
Qed.

Example flj: fLeibniz trueEquality.
Proof.
  intros x y f xy. unfold trueEquality in xy. subst. reflexivity. Qed.

Proposition characterization: ∀ J, (RL J ↔ ∀ x y, J x y ↔ x = y).
                    (* only extensionally: we can't say J = (=)! *)
Proof.
  intros J. split; intros hyp.
  - destruct hyp as (rj & lj). intros x y. split; intros xy.
    + apply lj with x.
      * assumption.
      * reflexivity.
    + subst. apply rj.
  - split.
    + intros x. apply hyp. reflexivity.
    + intros x y P Jxy Px. apply hyp in Jxy. subst. assumption.
Qed.
(* But the characterization doesn't hold for functional Leibniz
   property. If X has at least 2 elements and J is universal,
   it's obviously reflexive and fLeibniz, but it's not equality. *)

End Equality_Characterization.

Section Equivalence_Calculus.

(* Šika proposes using ≡ as a base for defining propositional
   logic, later adding ∨ to get a positive fragment and
   yet later adding ¬ to get the whole thing. Axioms:
   
   Associativity of ≡ (so parentheses aren't needed:)
   Commutativity of ≡: x≡y≡y≡x
   Associativity of ∨
   Commutativity of ∨
   Idempotence of ∨
   Distributivity of ∨ over ≡
   
   Half-distributivity of ¬ over ≡: ¬(x≡y)≡x≡¬y
    => DNE ¬¬x≡x
   Tertium non datur: x∨¬x
*)

Variable (B: Set) (ekviv: B → B → B).
Notation "x ≡ y" := (ekviv x y) (left associativity, at level 90).
Definition true x := x = (x ≡ x). Coercion true : B >-> Sortclass.
(* That means we can assert elements of B as propositions,
   and proving x actually means proving "true x" (x = (x ≡ x)). *)

Axiom eA: ∀ x y z, (x ≡ y ≡ z) ≡ (x ≡ (y ≡ z)).
Axiom eS: ∀ x y, x ≡ y ≡ y ≡ x.

Lemma ejj: ∀ x y, x ≡ y ↔ x = y.
Proof.
  apply characterization. split.
  - intros x. unfold true. (* now what? *) admit.
  - intros x y P xy px. (* even more hopeless *) admit.
Admitted.

(* One minor problem with defining t as y≡y: we must first have y.
   Bigger problem: To be able to rewrite using ≡, we must first
   have fLeibniz property (with respect to itself). However, this
   only follows from associativity _if_ you already can rewrite
   ("remove parentheses"). It is circular after all. :-( *)

Definition associative {X: Set} (op: X → X → X) := ∀ x y z,
  op x (op y z) = op (op x y) z.

Proposition eAj: associative ekviv.
Proof. intros x y z. symmetry. apply ejj. apply eA. Qed.

Proposition yyl1: ∀ x y, x ≡ ((y ≡ y) ≡ x).
Proof. intros x y. rewrite 2 eAj. apply eS. Qed.

Section Properties_Operation_Relation.

Variable (X: Set) (op: X → X → X).
Notation "x ○ y" := (op x y) (at level 65).
Definition R x y := x ○ y = y.
Notation "x # y" := (R x y) (at level 75).

Definition idempotent := ∀ x, x ○ x = x.
Proposition i2r: idempotent ↔ reflexive X R.
Proof. split; intros hyp x; apply hyp. Qed.

Definition absorbent t := ∀ x, x ○ t = t.
Definition maximal t := ∀ x, x # t.
Proposition a2m: ∀ t, absorbent t ↔ maximal t.
Proof. split; intros hyp x; apply hyp. Qed.

Definition transitive := ∀ x y z, x # y → y # z → x # z.
Proposition as2tr: associative op → transitive.
Proof.
  intros assoc x y z xy yz. unfold "#" in *.
  rewrite <- yz, assoc, xy. reflexivity.
Qed.
(* Converse doesn't hold here: on {t,f}, define x○y:=¬y.
   Then # is empty (x○y is never y) so trivially transitive,
   but t○(t○t)=t○f=t and (t○t)○t=f○t=f, so ○ is not associative. *)

(* Also: if ○ is commutative, then # is antisymmetric.
   The converse doesn't hold; same counterexample. *)
   
(* Also, what distributes through ○, is monotone with respect to #.
   Again, the same counterexample (with ∧ as additional operation)
   shows that converse doesn't hold. *)

End Properties_Operation_Relation.

(* The mystery of quasidistributivity *)
(* ---------------------------------- *)

(* ∨ distributes over ≡, but ∧ doesn't.
   There is a "quasidistributivity": ∧ distributes over ternary ≡!
   Of course, then ∨ also distributes over ternary ≡ (which is
   not surprising, since ternary ≡ is invariant to t↔f switch *)
   
(* | x  y     | is a square with "even parity".      | x  x∧y |
   | z  x≡y≡z |                                 Also | y  x∨y | *)

(* However, why does ∨ behave even better?
   Of course, if we want symmetry swapping ∨ and ∧, we also have
   to switch t↔f, and then binary ≡ becomes ⊻ (xor), but
   ternary ≡ is preserved (see squares above)

(* In | x y | there is an odd number of t and even number of f
      | x≡y |   so we can't just swap them: we get x⊻y below *)

(* And truly, ∧ distributes over ⊻: x∧(y⊻z) ≡ x∧y ⊻ x∧z.
   But ≡ can be used for rewriting, since it's transitive!
   Well, what does transitive mean? (x≡y)∧(y≡z)→(x≡z)
   Dually, we get a contrapositive: (x⊻y)∨(y⊻z)←(x⊻z) which holds.

And there is also a reason for extra-good property:
in Z2 (a ring of two elements, even and odd numbers)
* if we interpret t as even (0), and f as odd (1),
  then ⊻ is addition (mod 2),
  and ∧ is multiplication (mod 2 but irrelevant)
  - so this is distributivity of multiplication over addition!
    (this is well known, but the dual interpretation maybe isn't:)
* if we interpret t as odd (1), and f as even (0),
  then ≡ is addition (mod 2),
  and ∨ is multiplication (mod 2 but irrelevant)
  - so this is again distributivity of times over plus! :-)
I think it solves the mystery. *)

(* Šika: which axioms should be used for ≡ & ∧ ?
  Yes, quasidistributivity, probably, but with ∧ there is another
  natural choice for an axiom (that we don't have with ∨, again
  since t is favored over f): x ∧ t ≡ x. I think it doesn't follow
  from anything else, and it (at least a bit) restores the
  "disadvantage" that ∧ has over ∨ regarding distributivity. *)

(* ≡ and ∨ formalize exactly the positive fragment.
   Normal forms: ≡-chains of very elementary disjunctions
   (no negations, no repetition, order doesn't matter)
   So with x and y we have ≡-chains of: x y x∨y, which are
   (again, no repetition, order doesn't matter)
   x    y    x∨y    x≡y    x≡x∨y    y≡x∨y    x≡y≡x∨y
                             x←y       x→y       x∧y            *)
(* Does tertium non datur follow from other axioms? No! → Python *)

(* The simplest forms are (with ∨ as head) x∨¬x
   and (with ≡ as head) x∨f≡x. They cannot be simplified further.
   A 4-value countermodel shows it is not a consequence.
   (Just for humoristic value, there is a 2-value model, where
   ≡ and ∨ are interpreted as ordinary equivalence and disjunction
   while ¬ is interpreted as identity (!). It satisfies all the
   axioms except TND. *)