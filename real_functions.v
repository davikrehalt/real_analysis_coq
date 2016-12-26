Require Import Coq.Structures.GenericMinMax.
Require Import Bool.
Require Import Reals. (*assume Reals exist*)
Require Import Rminmax.
Require Import Eqdep. (*assume UIP*)
Open Scope R_scope.
Open Scope bool_scope.

Definition equivalence {T : Type} (R : T -> T -> Prop) :=
  (forall x:T, R x x) /\ (forall (x y:T), R x y -> R y x) /\ (forall (x y z:T), R x y -> R y z -> R x z).
Definition compatible {S T : Type} (R : T -> T -> Prop) (f : T -> S) := forall x y : T, R x y -> f x = f y.
Definition compatible_prop {S T : Type} (R : T -> T -> Prop) (f : T -> Prop) := forall x y : T, R x y -> (f x <-> f y).
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).
Hint Unfold compose.
Record Type_Quotient {T : Type} (equiv : T -> T -> Prop)  := {
  Hequiv : equivalence equiv;
  quo_type :> Type;
  class :> T -> quo_type;
  quo_comp : forall (x y : T), equiv x y -> class x = class y;
  quo_comp_rev : forall (x y : T), class x = class y -> equiv x y;
  quo_lift : forall (R : Type) (f : T -> R), compatible equiv f -> quo_type -> R;
  quo_lift_prop : forall (R : Type) (f : T -> R) (Hf : compatible equiv f) (x:T), (quo_lift R f Hf) (class x) = f x;
  quo_surj : forall (c : quo_type), exists (x : T), c = class x}.
Axiom Quotients_Exist : forall (T : Type) (equiv : T -> T -> Prop) (Hequiv:equivalence equiv), (Type_Quotient equiv).

Record Subtype {T:Type}(P : T -> Prop) := {
  subtype       :> Type;
  subtype_inj   :> subtype -> T;
  subtype_isinj : forall (s t:subtype), (subtype_inj s = subtype_inj t) -> s = t;
  subtype_h     : forall (x : T), P x -> (exists s:subtype,x = subtype_inj s);
  subtype_h0    : forall (s : subtype), P (subtype_inj s)}.

Axiom Subtypes_Exist : forall (T:Type)(P : T -> Prop), Subtype P.

Axiom Functional_Extensionality_Dep : forall {A} {B : A -> Type},
  forall (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.
Axiom Predicate_Extensionality : forall {A}(P Q : A -> Prop),(forall (x:A),P(x) <-> Q(x)) -> (P = Q).

Axiom FunctionalDependentChoice :
  forall (A : Type) (R:A->A->Prop), 
  (forall x:A, exists y:A, R x y) -> 
  (forall x0:A, exists f : nat -> A, f 0%nat = x0 /\ forall n, R (f n) (f (S n))).

Axiom supremum :forall E:R -> Prop,
    (exists l : R,is_upper_bound E l) -> (exists x : R, E x) ->
    { m:R | is_lub E m /\ (forall x:R, x<m -> exists y:R,(E y /\ y>x))}.

Record Normed_Space : Type := mknormspace
  {Vspace     :> Type;
   add        : Vspace -> Vspace -> Vspace;
   neg        : Vspace -> Vspace;
   scalar_mul : R -> Vspace -> Vspace;
   zero       : Vspace;
   norm       : Vspace -> R;
   add_assoc  : forall x y z:Vspace, add x (add y z) = add (add x y) z;
   add_comm   : forall x y:Vspace, add x y = add y x;
   add_inv    : forall x:Vspace, add x (neg x) = zero;
   add_id     : forall x:Vspace, add x zero = x;
   mul_assoc  : forall (x:Vspace) (a b:R), scalar_mul a (scalar_mul b x) = scalar_mul (a*b) x;
   mul_id     : forall x:Vspace, scalar_mul 1 x = x;
   mul_dist1  : forall (x:Vspace) (a b:R), scalar_mul (a+b) x = add (scalar_mul a x) (scalar_mul b x);
   mul_dist2  : forall (x y:Vspace) (a:R), scalar_mul a (add x y) = add (scalar_mul a x) (scalar_mul a y);
   norm_pos1  : forall x:Vspace, (norm x >= 0);
   norm_pos2  : forall x:Vspace, (norm x = 0) -> (x=zero);
   norm_add   : forall x y:Vspace, norm (add x y) <= norm x + norm y;
   norm_multi : forall (x:Vspace) (a:R), norm (scalar_mul a x) = (Rabs a)*(norm x)}.
Theorem T1 : forall x y z:R, x+(y+z)=(x+y)+z.
Proof. 
  intros x y z.
  rewrite Rplus_assoc.
  trivial.
Qed.

Theorem T2 : forall x y:R, x+y=y+x.
Proof.
  exact Rplus_comm.
Qed.

Theorem T3 : forall x:R, x+(-x)=0.
Proof.
  exact Rplus_opp_r.
Qed.

Theorem T4 : forall x:R, x+0=x.
Proof.
  exact Rplus_0_r.
Qed.

Theorem T5 : forall (x:R) (a b:R), a*(b*x) = (a*b)*x.
Proof.
  intros x a b.
  rewrite (Rmult_assoc a b x).
  trivial.
Qed.

Theorem T6 : forall (x:R), 1*x=x.
Proof.
  exact Rmult_1_l.
Qed.

Theorem T7 : forall (x:R) (a b:R), (a+b)*x=a*x+b*x.
Proof.
  intros x a b.
  rewrite (Rmult_plus_distr_r).
  trivial.
Qed.

Theorem T8 : forall (x y:R) (a:R),  a*(x+y) = a*x+a*y.
Proof.
  intros x y a.
  rewrite (Rmult_plus_distr_l a x y).
  trivial.
Qed.

Theorem T9a : forall (x:R), Rabs x >= 0.
Proof.
  intros x.
  apply Rle_ge.
  apply Rabs_pos.
Qed.

Theorem T9b : forall (x:R), Rabs x = 0 -> x = 0.
Proof.
  intros x.
  pose (eq := total_order_T x 0).
  pose (eq0 := Rabs_pos_lt x).
  case eq.
  intros eq1.
  case eq1.
  intros eq2.
  pose (eq3 := eq0 (Rlt_not_eq x 0 eq2)).
  intros eq4.
  rewrite eq4 in eq3. 
  pose (h:= Rlt_irrefl 0 eq3).
  tauto.
  tauto.
  intros eq1.
  pose (eq2 := eq0 (Rgt_not_eq x 0 eq1)).
  intros eq3.
  rewrite eq3 in eq2. 
  pose (h:= Rlt_irrefl 0 eq2).
  tauto.
Qed.

Theorem T9c : forall (x y:R), Rabs (x + y) <= Rabs x + Rabs y.
Proof.
  intros x y.
  apply Rabs_triang.
Qed.

Theorem T10 : forall (x:R) (a:R), Rabs (a*x) = (Rabs a)*(Rabs x).
Proof.
  intros x a.
  apply (Rabs_mult a x). 
Qed.

Theorem R1 : forall (x y:R),(x>=0)->(y>=0)->(x+y=0)->(x=0 /\ y=0).
Proof.
  intros.
  pose (Rplus_ge_compat_r y x 0 H).
  rewrite H1 in r.
  rewrite Rplus_0_l in r.
  destruct (Rge_ge_eq y 0).
  assert (y>=0 /\ 0>=y).
  tauto.  
  pose (H2 H4).
  rewrite e in H1.
  rewrite Rplus_0_r in H1.
  tauto.
Qed.
Theorem R2 :forall (x y:R), 0<x -> 0<y -> 0 < Rmin x y.
Proof.
  intros x y.
  intros H1 H2.
  apply R.min_glb_lt.
  tauto.
  tauto.  
Qed.

Definition is_lower_bound (E:R -> Prop) (m:R) := forall x:R, E x -> m <= x.

Definition is_glb (E:R -> Prop) (m:R) :=
  (is_lower_bound E m) /\ (forall b:R, is_lower_bound E b -> b <= m).

Definition neg_set (E:R -> Prop) := fun x=> E (-x).

Theorem R3 : forall (E:R -> Prop)(x:R), is_upper_bound E x <-> is_lower_bound (neg_set E) (-x).
Proof.
  intros.  
  split.
  intros H.
  unfold is_upper_bound in H.
  unfold is_lower_bound.
  intros x0.
  unfold neg_set.  
  intros H0.
  pose (H1:=Ropp_le_contravar).
  pose (H2:=Ropp_involutive).
  rewrite <- H2.
  apply H1.
  apply H.
  tauto.
  intros H.
  unfold is_upper_bound.
  unfold is_lower_bound in H.
  intros x0.
  intros H0.
  pose (H1:= Ropp_le_contravar).
  pose (H2:= H (-x0)).
  unfold neg_set in H2.
  pose (H3:=Ropp_involutive).
  rewrite H3 in H2.  
  pose (H4 := H2 H0).
  pose (H5:= H1 _ _ H4).
  congruence. 
Qed.  

Theorem R4 :forall (E:R -> Prop), bound E <-> (exists x:R, is_lower_bound (neg_set E) x).
Proof.
  intros.
  split.
  intros H.
  destruct H.
  exists (-x).
  apply R3.
  trivial.
  intros H.
  destruct H.
  exists (-x).
  apply R3.
  rewrite Ropp_involutive.
  trivial.  
Qed.

Theorem R5 :forall (E:R -> Prop), neg_set (neg_set E) = E.
Proof.
  intros E.
  apply Predicate_Extensionality.
  intros x.  
  split.
  intros H.
  unfold neg_set in H.
  rewrite Ropp_involutive in H.
  trivial.
  intros H.
  unfold neg_set.
  rewrite Ropp_involutive.
  trivial.
Qed.

Theorem R6 : forall (E:R -> Prop)(x:R), is_lub E x <-> is_glb (neg_set E) (-x).
Proof.
  intros.
  split.
  intros H.
  unfold is_glb.
  split.
  destruct H.
  apply R3.
  trivial.
  intros l H0.
  pose (H1 := R3 E (-l)).  
  destruct H1.
  rewrite Ropp_involutive in H2.  
  pose (H3 := H2 H0).
  destruct H.
  pose (H5 := H4 (-l) H3).
  Check Ropp_le_contravar.
  pose (H6 := Ropp_le_contravar _ _ H5).
  rewrite Ropp_involutive in H6.
  trivial.  
  intros H.
  unfold is_lub.
  split.
  destruct H.
  apply R3.
  trivial.
  intros b H0.
  pose (H1 := R3 E b).  
  destruct H1.
  pose (H3 := H1 H0).
  destruct H.
  pose (H5 := H4 (-b) H3). 
  pose (H6 := Ropp_le_contravar _ _ H5).
  rewrite Ropp_involutive in H6.
  rewrite Ropp_involutive in H6.
  trivial.  
Qed.

Theorem infimum :forall E:R -> Prop,
    (exists l : R,is_lower_bound E l) -> (exists x : R, E x) ->
    { m:R | is_glb E m /\ (forall x:R,x>m -> (exists y:R,(E y /\ y<x)))}.
  intros.
  pose (E1 := neg_set E).
  assert (bound E1) as H1.
  apply R4.  
  unfold E1.
  rewrite R5.
  trivial.
  assert (exists x:R, E1 x) as H2.
  destruct H0.
  exists (-x).
  unfold E1.
  unfold neg_set.
  rewrite Ropp_involutive.
  trivial.
  pose (x:=supremum E1 H1 H2).
  destruct x.  
  pose (R6 E1 x). 
  exists (-x).
  split.
  destruct i.
  destruct a.
  unfold E1 in H3.
  rewrite R5 in H3.
  tauto.
  intros.
  destruct a.
  pose (H5 (-x0)).
  pose (Ropp_gt_lt_contravar _ _ H3).
  rewrite Ropp_involutive in r.
  pose (e r).
  destruct e0.
  exists (-x1).
  split.
  destruct H6.
  tauto.
  destruct H6.  
  pose (Ropp_gt_lt_contravar _ _ H7).
  rewrite Ropp_involutive in r0.
  trivial.
Qed.  

Theorem infimum_unique :forall (E:R -> Prop)(a b:R),
    is_glb E a -> is_glb E b -> a=b.
Proof.
  intros.  
  unfold is_glb in H.
  unfold is_glb in H0.
  destruct H,H0.
  pose (H2 _ H).
  pose (H1 _ H0).
  apply Rle_le_eq.
  split.
  trivial.
  trivial.
Qed.
  
Theorem R7 : 1 + 1 > 0.
Proof.
  pose (Rlt_gt _ _ Rlt_0_1).
  pose (Rplus_gt_compat_l 1 1 0 r). 
  refine (Rgt_trans 2 1 0 _ _). 
  rewrite <- Rplus_0_r.
  trivial.
  trivial.
Qed.
Theorem R8: (1/2+1/2 = 1).
Proof.
  simpl.
  field. 
Qed.

Theorem R9: forall (a b:R),(forall p:posreal,a+p>b) -> a>=b.
Proof.
  intros.
  pose (Rge_gt_dec a b).
  destruct s. 
  trivial.
  pose (Rgt_minus b a r).
  pose (mkposreal (b-a) r0).
  pose (H p).
  unfold p in r1.
  assert (a+(b-a) > b).
  tauto.
  assert (a+(b-a)=b).
  field.
  rewrite H1 in H0.
  pose (Rgt_irrefl _ H0).
  tauto.
Qed.

Definition mul_set (E:R -> Prop) (a:R) := fun x=> exists u:R,E u /\ x = a*u.

Theorem R10 : forall (E:R -> Prop)(a:R)(x:R),
 (a>0) -> (is_glb E x <-> is_glb (mul_set E a) (a*x)).
Proof.
  intros.
  split.
  intros H0.
  unfold is_glb.
  split.
  unfold is_lower_bound.
  intros x0.
  destruct H0.
  unfold is_lower_bound in H0.
  pose (H0 x0).
  intros. 
  unfold mul_set in H2.
  destruct H2.
  destruct H2.
  rewrite H3.
  apply Rmult_le_compat_l. 
  apply Rlt_le.
  apply Rgt_lt.
  trivial.
  pose (H0 x1 H2).
  tauto.
  intros b.
  intros H1.
  destruct H0.
  assert ((is_lower_bound E) (b/a)).
  unfold is_lower_bound.
  intros x0.
  intros.
  unfold is_lower_bound in H1.  
  pose (H1 (a*x0)).  
  assert (mul_set E a (a*x0)).
  unfold mul_set.
  exists x0.
  tauto.
  pose (r H4).
  pose (Rmult_le_compat_r (/a) b (x0*a)).
  assert (/a >=0).
  pose (Rinv_0_lt_compat a).
  assert (0<a).
  apply Rgt_lt.
  trivial.
  pose (r2 H5).
  pose (Rlt_le 0 (/a) r3).
  apply Rle_ge.
  trivial.
  assert (0<=(/a)).
  apply Rge_le.
  trivial.
  pose (r1 H6).
  assert (b<=x0*a).
  rewrite Rmult_comm.
  trivial.
  pose (r2 H7).
  rewrite Rmult_assoc in r3.
  rewrite Rinv_r in r3.
  rewrite Rmult_1_r in r3.
  auto.
  apply Rgt_not_eq.
  trivial.
  pose (H2 _ H3).
  pose (Rmult_le_compat_l a (b/a) x).
  assert (0<=a).
  apply Rlt_le.
  apply Rgt_lt.
  trivial.
  assert (a*(b/a) = b).
  field.
  apply Rgt_not_eq.
  trivial.
  rewrite H5 in r0.
  pose (r0 H4 r).
  trivial.
  intros H0.
  unfold is_glb.
  split.
  unfold is_lower_bound.
  intros x0.
  intros.
  unfold is_glb in H0.
  destruct H0.  
  unfold is_lower_bound in H0.
  pose (H0 (x0 * a)).
  unfold mul_set in r.
  assert (exists u:R,E u /\ x0*a =a*u).  
  exists x0.
  rewrite Rmult_comm.
  tauto.
  pose (r H3).
  rewrite Rmult_comm in r0.
  pose (Rmult_le_compat_r (/a) (x*a) (x0*a)).
  assert (0<=(/a)).
  apply Rlt_le.
  apply Rinv_0_lt_compat.
  apply Rgt_lt.
  trivial.
  pose (r H3).
  pose (r1 H4 r0).
  assert (x*a*/a=x).
  field.  
  apply Rgt_not_eq.
  trivial.
  assert (x0*a*/a=x0).
  field.  
  apply Rgt_not_eq.
  trivial.
  rewrite H5 in r3.
  rewrite H6 in r3.
  trivial.
  intros b.
  intros.  
  unfold is_glb in H0.
  destruct H0.
  assert (is_lower_bound (mul_set E a) (a*b)).
  unfold is_lower_bound.
  intros x0.
  intros.
  destruct H3.
  destruct H3.
  rewrite H4.  
  apply (Rmult_le_compat_l (a) (b) (x1)).
  apply Rlt_le.
  apply Rgt_lt.
  trivial.
  unfold is_lower_bound in H1.
  exact (H1 x1 H3).
  pose (H2 (a*b) H3).
  assert ((/a)*a*b<=(/a)*a*x).
  rewrite Rmult_assoc.
  rewrite Rmult_assoc.
  apply (Rmult_le_compat_l (/a) (a*b) (a*x)).
  pose (Rinv_0_lt_compat).
  Check Rgt_lt.
  pose (r0 a (Rgt_lt a 0 H)).
  apply Rlt_le.
  trivial.
  trivial.
  assert (/a*a*b=b).
  field.  
  apply Rgt_not_eq.
  trivial.
  assert (/a*a*x=x).
  field.  
  apply Rgt_not_eq.
  trivial.
  congruence.
Qed.
  
Definition R_Space := mknormspace R Rplus Ropp Rmult 0 Rabs T1 T2 T3 T4 T5 T6 T7 T8 T9a T9b T9c T10.
Check R_Space.

Theorem V1 : forall (V : Normed_Space) (x:Vspace V), scalar_mul V 0 x = zero V.
Proof.
  intros W x.
  pose (eq := T4 0). 
  assert (scalar_mul W 0 x = (add W) (scalar_mul W 0 x) (scalar_mul W 0 x)).
  pose (eq0 := mul_dist1 W x 0 0 ).
  congruence.
  pose (add_inv W (scalar_mul W 0 x)).
  pose (k := scalar_mul W 0 x).
  assert (k = scalar_mul W 0 x).
  tauto.
  assert (add W k k = k).
  symmetry.
  tauto.
  assert (add W k (neg W k) = add W (add W k k) (neg W k)).
  congruence.
  pose (eq1 := add_assoc W k k (neg W k)).
  pose (eq2 := add_inv W k).
  assert (add W (add W k k) (neg W k) = k).
  transitivity (add W k (zero W)).
  congruence.
  apply (add_id W).  
  assert (zero W = k).
  congruence.
  congruence.
Qed.

Theorem V2 : forall (V : Normed_Space), norm V (zero V) = 0.
Proof.
  intros W.
  pose (V1 W (zero W)).
  assert (norm W (scalar_mul W 0 (zero W)) = 0).
  pose (eq := norm_multi W (zero W) 0).
  pose (Rabs_R0).
  pose (Rmult_0_l (norm W (zero W))).
  congruence.
  congruence.
Qed.  

Theorem V3 : forall (V:Normed_Space),  neg V (zero V) = zero V.
Proof.
  intros V.
  pose (H := add_inv V (zero V)).
  pose (H2 := add_comm V (zero V) (neg V (zero V))).
  pose (H3 := add_id V (neg V (zero V))).
  transitivity (add V (zero V) (neg V (zero V))). 
  transitivity (add V (neg V (zero V)) (zero V)).
  symmetry.
  trivial.  
  symmetry.
  trivial.
  trivial.  
Qed.

Theorem V4 : forall (V: Normed_Space) (x:Vspace V), add V x (neg V (zero V)) = x.
Proof.
  intros V x.  
  pose (H0 := V3 V).
  rewrite H0.
  apply add_id.  
Qed.

Theorem V5 : forall (V : Normed_Space)(a : V), add V (zero V) a = a.
Proof.
  intros V a.
  transitivity (add V a (zero V)).
  refine (add_comm _ _ _).
  apply add_id.
Qed.

Theorem V6 : forall (V : Normed_Space)(a:V), add V (neg V a) a = zero V.
Proof.
  intros V a.
  transitivity (add V a (neg V a)).
  apply add_comm.
  apply add_inv.
Qed.

Theorem V7 : forall (V : Normed_Space)(a b : V), add V (neg V a) (add V a b) = b.
Proof.
  intros V a b.
  symmetry.
  transitivity (add V (add V (neg V a) a) b).
  symmetry.
  rewrite V6.
  apply V5.
  symmetry.
  apply add_assoc.
Qed.

Theorem V8 : forall (V : Normed_Space)(a b c : V), (add V a c = add V a b) <-> (b = c).
Proof.
  intros V a b c.
  split.
  intros h.
  transitivity (add V (neg V a) (add V a b)).
  symmetry.
  apply V7.
  rewrite <- h.
  apply V7.
  intros h.
  rewrite <- h.
  tauto.
Qed.
  
Theorem V9 : forall (V: Normed_Space)(x:V), neg V (neg V x) = x.
Proof.
  intros V x.
  rewrite <- (V8 V (neg V x) (neg V (neg V x)) x).
  rewrite add_inv.
  rewrite add_comm.
  rewrite add_inv.
  tauto.
Qed.
Theorem V10 : forall {V:Normed_Space}(a b:V), add V (neg V a) (neg V b) = neg V (add V a b).
Proof.
  intros V.
  intros a b.
  rewrite <- (V8 V (add V a b)). 
  rewrite add_inv.
  rewrite add_assoc.
  replace (add V (add V a b) (neg V a)) with (add V b (add V a (neg V a))). 
  rewrite add_inv.
  rewrite add_id.
  rewrite add_inv.
  trivial.
  rewrite add_assoc.
  rewrite <- (add_comm V a b).
  trivial.
Qed.

Theorem V11 : forall {V:Normed_Space}(a b:V), (neg V a = neg V b) <-> a=b.
Proof.
  intros V a b.  
  split.
  intros H.
  rewrite <- (V8 V (neg V a)).  
  rewrite <- (add_comm V a (neg V a)).
  rewrite add_inv.
  rewrite <- (V8 V (neg V b)).
  rewrite add_id.
  rewrite add_comm.
  rewrite <- add_assoc.
  rewrite add_inv.
  rewrite add_id.
  congruence.
  intros H.
  congruence.  
Qed.

Theorem V12 : forall {V:Normed_Space}(a:V), (neg V a = scalar_mul V (-1) a).
Proof.
  intros.
  pose (H:= V8 V a (neg V a) (scalar_mul V (-1) a)).  
  destruct H.  
  apply H.
  rewrite <- (mul_id V (a)) at 1.
  rewrite <- mul_dist1.
  assert (1+(-1) =0).
  apply Rplus_opp_r.
  rewrite H1.
  rewrite add_inv.
  rewrite V1.
  trivial.
Qed.

Definition NormProductSet  (W1 W2 : Normed_Space) : Type := prod (Vspace W1) (Vspace W2).
Definition NormProductAdd  (W1 W2 : Normed_Space) (x y: NormProductSet W1 W2) : NormProductSet W1 W2 :=
  match x,y with
  |(x1,x2),(y1,y2) => (add W1 x1 y1,add W2 x2 y2)
  end. 
Definition NormProductNeg  (W1 W2 : Normed_Space) (x : NormProductSet W1 W2) : NormProductSet W1 W2 :=
  match x with
  |(x1,x2) => (neg W1 x1,neg W2 x2)
  end. 
Definition NormProductZero  (W1 W2 : Normed_Space) : NormProductSet W1 W2 := (zero W1,zero W2).
Definition NormProductMul  (W1 W2 : Normed_Space) (a:R) (x: NormProductSet W1 W2) : NormProductSet W1 W2 :=
  match x with
  |(x1,x2) => (scalar_mul W1 a x1 ,scalar_mul W2 a x2)
  end. 
Definition NormProductNorm  (W1 W2 : Normed_Space) (x: NormProductSet W1 W2) : R :=
  match x with
  |(x1,x2) => (norm W1 x1)+(norm W2 x2) 
  end. 
Theorem T11 : forall (W1 W2 : Normed_Space) (x y z: NormProductSet W1 W2), NormProductAdd W1 W2 x (NormProductAdd W1 W2 y z) = NormProductAdd W1 W2(NormProductAdd W1 W2 x y) z.
Proof.
  intros W1 W2 x y z.
  destruct x,y,z.
  unfold NormProductAdd.
  assert (add W1 v (add W1 v1 v3) = add W1 (add W1 v v1) v3).
  apply (add_assoc W1).
  assert (add W2 v0 (add W2 v2 v4) = add W2 (add W2 v0 v2) v4).
  apply (add_assoc W2).
  congruence.
Qed.

Theorem T12 : forall (W1 W2 : Normed_Space) (x y: NormProductSet W1 W2), NormProductAdd W1 W2 x y = NormProductAdd W1 W2 y x.
Proof.
  intros W1 W2 x y.
  destruct x,y.
  unfold NormProductAdd.
  pose (add_comm W1 v v1).
  pose (add_comm W2 v2 v0).
  congruence.
Qed.

Theorem T13 : forall (W1 W2 : Normed_Space) (x : NormProductSet W1 W2), NormProductAdd W1 W2 x (NormProductNeg W1 W2 x) = NormProductZero W1 W2.
Proof.
  intros W1 W2 x.
  destruct x.
  unfold NormProductNeg, NormProductAdd, NormProductZero.
  pose (add_inv W1 v).
  pose (add_inv W2 v0).
  congruence.
Qed.

Theorem T14 : forall (W1 W2 : Normed_Space) (x: NormProductSet W1 W2), NormProductAdd W1 W2 x (NormProductZero W1 W2) = x.
Proof.
  intros W1 W2 x.
  destruct x.
  unfold NormProductAdd, NormProductZero.
  pose (add_id W1 v).
  pose (add_id W2 v0).
  congruence.
Qed.

Theorem T15 : forall (W1 W2 : Normed_Space) (x: NormProductSet W1 W2) (a b:R), NormProductMul W1 W2 a (NormProductMul W1 W2 b x) = NormProductMul W1 W2 (a*b) x.
Proof.
  intros W1 W2 x a b.
  destruct x.
  unfold NormProductMul.
  pose (mul_assoc W1 v a b).
  pose (mul_assoc W2 v0 a b).
  congruence.
Qed.

Theorem T16 : forall (W1 W2 : Normed_Space) (x: NormProductSet W1 W2), NormProductMul W1 W2 1 x = x. 
Proof.
  intros W1 W2 x.
  destruct x.
  unfold NormProductMul.
  pose (mul_id W1 v).
  pose (mul_id W2 v0).
  congruence.
Qed.

Theorem T17 : forall (W1 W2 : Normed_Space) (x: NormProductSet W1 W2) (a b:R),
    NormProductMul W1 W2 (a+b) x = NormProductAdd W1 W2 (NormProductMul W1 W2 a x) (NormProductMul W1 W2 b x).
Proof.
  intros W1 W2 x a b.
  destruct x.
  unfold NormProductMul,NormProductAdd.
  pose (mul_dist1 W1 v a b).
  pose (mul_dist1 W2 v0 a b).
  congruence.
Qed.
Theorem T18 : forall (W1 W2 : Normed_Space) (x y : NormProductSet W1 W2) (a:R),
    NormProductMul W1 W2 a (NormProductAdd W1 W2 x y) = NormProductAdd W1 W2 (NormProductMul W1 W2 a x) (NormProductMul W1 W2 a y).
Proof.
  intros W1 W2 x y a.
  destruct x, y.
  unfold NormProductMul, NormProductAdd.
  pose (mul_dist2 W1 v v1 a).
  pose (mul_dist2 W2 v0 v2 a).
  congruence.
Qed.

Theorem T19a : forall (W1 W2 : Normed_Space) (x: NormProductSet W1 W2), NormProductNorm W1 W2 x >= 0.
Proof.
  intros W1 W2 x.
  destruct x.
  apply Rle_ge.
  apply Rplus_le_le_0_compat.
  apply Rge_le.
  apply norm_pos1.
  apply Rge_le.
  apply norm_pos1.
Qed.  

Theorem T19b : forall (W1 W2 : Normed_Space) (x: NormProductSet W1 W2), (NormProductNorm W1 W2 x = 0)-> (x=NormProductZero W1 W2).
Proof.
  intros W1 W2 x.
  destruct x.
  unfold NormProductZero, NormProductNorm.
  pose (eq0 := norm_pos1 W1 v).
  pose (eq1 := norm_pos1 W2 v0).
  pose (eq2 := norm_pos2 W1 v).
  pose (eq3 := norm_pos2 W2 v0).
  intros.
  pose (R1 _ _ eq0 eq1 H).
  destruct a.
  pose (eq2 H0).
  pose (eq3 H1).
  congruence.
Qed.

Theorem T19c : forall (W1 W2 : Normed_Space) (x1 x2 : NormProductSet W1 W2),
    (NormProductNorm W1 W2 (NormProductAdd W1 W2 x1 x2) <=
     NormProductNorm W1 W2 x1 + NormProductNorm W1 W2 x2).
Proof.
  intros W1 W2 x1 x2.
  destruct x1, x2 .
  unfold NormProductAdd. 
  unfold NormProductNorm. 
  pose (H := norm_add W1 v v1).
  pose (H0 := norm_add W2 v0 v2).
  pose (H1 := Rplus_le_compat_l (norm W2 (add W2 v0 v2))).
  pose (H2 := H1 (norm W1 (add W1 v v1)) (norm W1 v+ norm W1 v1) H).
  refine (Rle_trans _ _ _ _ _).
  rewrite Rplus_comm in H2.
  exact H2.
  rewrite Rplus_comm .
  rewrite Rplus_assoc .
  rewrite Rplus_assoc .
  apply (Rplus_le_compat_l).  
  rewrite Rplus_comm.
  rewrite (Rplus_comm (norm W1 v1) (norm W2 v2)).
  rewrite <- Rplus_assoc.
  apply Rplus_le_compat_r.
  apply norm_add.
Qed.

Theorem T20 : forall (W1 W2 : Normed_Space) (x: NormProductSet W1 W2) (a:R),
    NormProductNorm W1 W2 (NormProductMul W1 W2 a x) = (Rabs a)*(NormProductNorm W1 W2 x).
Proof.
  intros W1 W2 x a.
  destruct x.
  unfold NormProductNorm,NormProductMul.
  pose (norm_multi W1 v a).
  pose (norm_multi W2 v0 a).
  pose (T8 (norm W1 v) (norm W2 v0) (Rabs a)).
  congruence.
Qed.

Definition NormSpaceProduct (W1 W2 : Normed_Space) : Normed_Space :=
  let W := NormProductSet W1 W2 in
  let Wplus := NormProductAdd W1 W2 in
  let Wneg := NormProductNeg W1 W2 in
  let Wmul := NormProductMul W1 W2 in
  let Wzero := NormProductZero W1 W2 in
  let Wnorm := NormProductNorm W1 W2 in
  let t1 := T11 W1 W2 in
  let t2 := T12 W1 W2 in
  let t3 := T13 W1 W2 in
  let t4 := T14 W1 W2 in
  let t5 := T15 W1 W2 in
  let t6 := T16 W1 W2 in
  let t7 := T17 W1 W2 in
  let t8 := T18 W1 W2 in
  let t9a := T19a W1 W2 in
  let t9b := T19b W1 W2 in
  let t9c := T19c W1 W2 in
  let t10 := T20 W1 W2 in
  mknormspace W Wplus Wneg Wmul Wzero Wnorm t1 t2 t3 t4 t5 t6 t7 t8 t9a t9b t9c t10.

Definition map_add (V W:Normed_Space)(f:V->W) :=
  forall (x y:V), (f (add V x y)) = (add W (f x) (f y)).
Definition map_homog (V W:Normed_Space)(f:V->W) :=
  forall (x:V) (a:R), (f (scalar_mul V a x)) = (scalar_mul W a (f x)).
Definition map_bdd (V W:Normed_Space)(f:V->W) :=
  exists C:posreal, forall (x:V), norm W (f x) <= C*(norm V x).
Definition bounded_map (V W:Normed_Space)(f:V->W) :=  (map_add V W f) /\ (map_homog V W f) /\ (map_bdd V W f).
Definition Hom (V W:Normed_Space) := Subtypes_Exist (V->W) (bounded_map V W).

Definition dist {V:Normed_Space} (x y: Vspace V) : R := norm V (add V y (neg V x)).

Theorem T20a :forall {V:Normed_Space} (x y: Vspace V),dist x y >=0.
Proof.
  intros.
  unfold dist.
  apply norm_pos1.
Qed.

Theorem T20b :forall {V:Normed_Space} (x y: Vspace V),dist x y = dist y x.
Proof.
  intros.
  unfold dist.
  cut (add V x (neg V y) = scalar_mul V (-1) (add V y (neg V x))).
  intros H.
  rewrite H.
  rewrite norm_multi.
  rewrite Rabs_Ropp.
  rewrite Rabs_R1. 
  rewrite Rmult_1_l.
  trivial.
  cut (scalar_mul V (-1) (add V y (neg V x)) = neg V (add V y (neg V x))).
  intros H.
  rewrite H.
  rewrite <- V10.
  rewrite V9.
  apply add_comm.
  symmetry.
  apply V12.  
Qed.  

Definition interior {V:Normed_Space} (A:V -> Prop) (x:V):=
  (exists eps:posreal,forall (y:Vspace V), (dist x y < eps) -> A y).

Definition closure {V:Normed_Space} (A:V -> Prop) (x:V):=
  forall eps:posreal, exists y:Vspace V, (A y) /\ (dist x y < eps).

Definition pre_dist_to_subset {V:Normed_Space}(A : V -> Prop)(x:V):(exists (y:V),A y) -> R -> Prop.
  intros H.
  exact (fun r:R => exists y:V,A y /\ dist x y = r).
  Defined.

Theorem T20c :forall {V:Normed_Space}(A : V -> Prop)(x:V)(f :exists (y:V),A y), is_lower_bound (pre_dist_to_subset A x f) 0.
Proof.
  intros.
  unfold is_lower_bound.
  intros.
  unfold pre_dist_to_subset in H.
  destruct H.
  destruct H.
  rewrite <- H0.
  apply Rge_le.
  apply T20a.
Qed.

Theorem T20d :forall {V:Normed_Space}(A : V -> Prop)(x:V)(f :exists (y:V),A y), exists (r:R), pre_dist_to_subset A x f r.
Proof.
  intros.
  destruct f.
  exists (dist x0 x).
  Check ex_intro.
  unfold pre_dist_to_subset.
  exists x0.
  split.
  tauto.
  apply T20b.
Qed.

Theorem pdist_to_subset: forall {V:Normed_Space}(A : V -> Prop)(x:V)(f : exists (y:V),A y)(rsubset := (pre_dist_to_subset A x f)),
  {r:R|is_glb rsubset r /\ (forall x : R, x > r -> exists y : R, rsubset y /\ y < x)}.
  intros.
  pose (Q := infimum (rsubset)).
  assert (exists s:R, is_lower_bound rsubset s).
  exists 0.
  apply T20c.
  assert (exists s:R, rsubset s).
  apply T20d.
  exact (Q H H0).
Qed.

Definition dist_to_subset {V:Normed_Space}(A : V -> Prop)(x:V)(f : exists (y:V),A y)(rsubset := (pre_dist_to_subset A x f)):R.
  destruct (pdist_to_subset A x f).
  exact x0.  
Defined.


Theorem dist_sub_pos {V:Normed_Space}(A : V -> Prop)(x:V)(f : exists (y:V),A y) : dist_to_subset A x f >=0.
Proof.
  intros.
  unfold dist_to_subset.
  pose (q := pdist_to_subset A x f).
  fold q .
  destruct q.
  destruct a.
  destruct H.
  pose (T20c A x f).
  pose (H1 _ i).
  apply Rle_ge.  
  trivial.
Qed.
  
Theorem T20e :forall {V:Normed_Space}(A : V -> Prop)(x:V)(f : exists (y:V), A y), dist_to_subset A x f = 0 -> closure A x.
Proof.
  intros.
  unfold closure.
  intros eps.
  unfold dist_to_subset in H.
  pose (q := pdist_to_subset A x f).
  fold q in H.
  destruct q.
  destruct a.
  rewrite H in H0.
  unfold is_glb in H0.
  destruct H0.
  rewrite H in H1.
  destruct eps.
  pose (H1 pos cond_pos).  
  destruct e.  
  destruct H3.
  unfold pre_dist_to_subset in H3.
  destruct H3.
  exists x2.  
  split.
  trivial.
  destruct H3.
  trivial.  
  destruct H3.
  rewrite H5.
  trivial.  
Qed.

Theorem T20f :forall {V:Normed_Space}(A : V -> Prop)(x:V)(f : exists (y:V), A y), closure A x -> dist_to_subset A x f = 0.
Proof.
  intros.
  unfold closure in H.
  unfold dist_to_subset.
  pose (q := pdist_to_subset A x f).
  pose (rsubset := pre_dist_to_subset A x f).
  fold rsubset in q.
  fold q.
  destruct q.
  destruct a.
  destruct H0.
  unfold is_lower_bound in H0.
  assert (forall x1:V, A x1 -> rsubset (dist x x1)).
  intros x1.
  unfold rsubset.
  unfold pre_dist_to_subset.
  exists x1.
  tauto.
  assert (forall r:posreal,x0 < r).
  intros r.
  pose (H r).
  destruct e.
  destruct H4.
  pose (H0 (dist x x1) (H3 x1 H4)).
  refine (Rle_lt_trans _ _ _ _ _).
  exact r0.
  trivial.
  pose (Rlt_le_dec 0 x0).
  destruct s.
  pose (mkposreal x0 r).  
  pose (H4 p).
  assert (x0<x0).
  tauto.  
  pose (Rlt_irrefl _ H5).
  tauto.
  assert (is_lower_bound rsubset 0).
  unfold is_lower_bound.
  intros x1.
  intros H5.
  unfold rsubset in H5.
  unfold pre_dist_to_subset in H5.
  destruct H5.
  destruct H5.
  rewrite <- H6.
  apply Rge_le.
  apply norm_pos1.
  pose (H2 _ H5).
  apply Rle_antisym.
  trivial.
  trivial.
Qed.  
  
Record Local_Function (Input_Space:Normed_Space) (Output_Space:Normed_Space) : Type := mklocalfunc
  {local_subset      : (Vspace Input_Space -> Prop);
   is_local_subset   : interior local_subset (zero Input_Space);
   local_function    : forall (x: Vspace Input_Space),(local_subset x -> Vspace Output_Space);
   local_function_h1 : forall (x: Vspace Input_Space) (h1 h2: local_subset x), local_function x h1 = local_function x h2}.

Definition eps_defined {V W:Normed_Space}(f:Local_Function V W)(eps:posreal):= (forall x:Vspace V,(norm V x < eps) -> local_subset V W f x).

Definition eps_same {V W:Normed_Space} (f g:Local_Function V W)(eps:posreal):= ((eps_defined f eps) /\ (eps_defined g eps)) /\
  (forall (p:eps_defined f eps)(q:eps_defined g eps)(x:Vspace V)(r : norm V x < eps),
  (local_function V W f x (p x r) = local_function V W g x (q x r))).
Definition locally_same (V W:Normed_Space) (f g: Local_Function V W) := exists eps:posreal,eps_same f g eps.
Theorem T20g : forall (V: Normed_Space) (x:Vspace V),dist (zero V) x = norm V x.
Proof.
  intros V x.  
  unfold dist.  
  pose (H := V4 V x).
  rewrite H.
  trivial.
Qed.

Definition pRmin (x y:posreal) : posreal := mkposreal (Rmin x y) (R2 x y (cond_pos x) (cond_pos y)).
Theorem T20h : forall (x y:posreal),  pRmin x y <= x.
Proof.
  intros x y.
  unfold pRmin.  
  apply R.le_min_l.
Qed.
Theorem T20i : forall (x y:posreal),  pRmin x y <= y.
Proof.
  intros x y.
  unfold pRmin.  
  apply R.le_min_r.
Qed.

Theorem T21 :forall (V W:Normed_Space), equivalence (locally_same V W).
Proof.
  intros V W.
  unfold equivalence.
  split.
  intros f.
  unfold locally_same.
  destruct f.
  destruct is_local_subset0.
  exists x.
  split.
  split.
  unfold eps_defined.
  assert (H := forall x0:Vspace V, norm V x0 < x -> local_subset0 x0). 
  intros x0.
  intros h.
  pose (h1 := T20g V x0).
  assert (dist (zero V) x0 < x).
  rewrite h1.
  trivial.
  apply l.
  trivial.
  unfold eps_defined.
  intros x0.
  intros h.
  pose (h1 := T20g V x0).
  assert (dist (zero V) x0 < x).
  rewrite h1.
  trivial.
  apply l.
  trivial.
  intros p q.
  intros x0 r0.
  apply local_function_h2.
  split.
  intros f g.
  intros h.
  destruct h.
  unfold locally_same.
  exists x.
  unfold eps_same.
  destruct H.
  split.
  tauto.
  intros p q x0 r.
  symmetry.
  apply H0.
  intros f g h.
  intros H1 H2.
  unfold locally_same.
  destruct H1.
  destruct H2.
  exists (pRmin x x0).
  unfold eps_same.
  destruct H.
  destruct H0.
  split.
  split.
  destruct H.
  unfold eps_defined.
  intros x1.
  intros H4.
  assert (norm V x1 < x).
  pose (H5:= T20h x x0).
  refine (Rlt_le_trans _ _ _ _ _).
  exact H4.
  exact H5.
  unfold eps_defined.
  apply H.
  tauto.
  destruct H0.
  unfold eps_defined.
  intros x1.
  intros H4.
  apply H3.
  refine (Rlt_le_trans _ _ _ _ _).
  exact H4.
  apply T20i.
  intros p q x1 r.
  assert (eps_defined g (pRmin x x0)).
  unfold eps_defined.
  intros x2.
  intros H3.
  destruct H0.
  apply H0.
  refine (Rlt_le_trans _ _ _ _ _).
  exact H3.
  apply T20i.
  transitivity (local_function V W g x1 (H3 x1 r)).
  assert (norm V x1 < x).
  refine (Rlt_le_trans _ _ _ _ _).
  exact r.
  apply T20h.
  destruct H. 
  pose (H6 := H1 H H5 x1 H4).
  transitivity (local_function V W f x1 (H x1 H4)).  
  apply local_function_h1.
  transitivity (local_function V W g x1 (H5 x1 H4)).
  apply H6.
  apply local_function_h1.
  assert (eps_defined g x0).
  tauto.
  assert (eps_defined h x0).
  tauto.
  assert (norm V x1 < x0).
  refine (Rlt_le_trans _ _ _ _ _).
  exact r.
  apply T20i.
  pose (H7 := H2 H4 H5 x1 H6).
  transitivity (local_function V W g x1 (H4 x1 H6)).
  apply local_function_h1.
  transitivity (local_function V W h x1 (H5 x1 H6)).
  tauto.
  apply local_function_h1.
Qed.

Theorem T21a : forall {V W:Normed_Space} (f : Local_Function V W), exists eps:posreal,eps_defined f eps.
Proof.
  intros V W f.
  destruct f.
  destruct is_local_subset0.
  exists x.
  unfold eps_defined.  
  intros x0.
  intros H.
  refine (l _ _).
  rewrite T20g.
  tauto.
Qed.  

Definition Locally_O {V W : Normed_Space} (f : Local_Function V W) := exists (delta:posreal) (C:posreal),
    ((eps_defined f delta) /\
     (forall (x:V), (norm V x < delta) -> (exists (p : local_subset V W f x),
                                   norm W (local_function V W f x p) <= C))).

Definition Locally_J {V W : Normed_Space} (f : Local_Function V W) := forall eps:posreal,exists (delta:posreal),
    ((eps_defined f delta) /\
     (forall (x:V), (norm V x < delta) -> (exists (p : local_subset V W f x),
                                   norm W (local_function V W f x p) <= eps))).

Definition Locally_o {V W : Normed_Space} (f : Local_Function V W) := forall eps:posreal,exists (delta:posreal),
    ((eps_defined f delta) /\
     (forall (x:V), (norm V x < delta) -> (exists (p : local_subset V W f x),
                                   norm W (local_function V W f x p) <= eps*(norm V x)))).

Record Injection (A B:Type) := {
  get_injection    :> A -> B;
  proof_injection  : forall (x y:A),(get_injection x = get_injection y) -> (x=y)}.

Definition Hom_inj : forall {V W:Normed_Space},Hom V W -> (V -> W).
  intros V W f.
  exact (subtype_inj _ (Hom V W) f).
Defined.

Record Norm_Embedding (V W:Normed_Space) := {
  norm_embedding   :> Hom V W;
  norm_embedding_h : forall (v:V), norm W (Hom_inj norm_embedding v) = norm V v}.

Record Closed_Subspace (V:Normed_Space) := {
  ext_closed_subspace :> Normed_Space;
  subspace_embedding  :> Norm_Embedding ext_closed_subspace V;
  int_closed_subspace : V -> Prop := fun (x:V) => exists (v:ext_closed_subspace), Hom_inj subspace_embedding v = x;
  subspace_closure : forall x:V, closure int_closed_subspace x <-> int_closed_subspace x}.

Definition closed_subspace_equiv {V : Normed_Space} (U:Closed_Subspace V) (x y:V) := exists z:U,(add V x (Hom_inj U z) = y).

Theorem T21f : forall (V : Normed_Space)(a b c : V), (add V a c = b) <-> (c = add V (neg V a) b).
Proof.
  intros V a b c.
  split.
  intros h.
  transitivity (add V (neg V a) (add V a c)).
  transitivity (add V (add V (neg V a) a) c).
  rewrite V6.
  symmetry.
  apply V5.
  symmetry.
  apply add_assoc.
  rewrite h.
  tauto.
  intros h.
  rewrite h.
  rewrite add_assoc.
  rewrite add_inv.
  rewrite add_comm.
  apply add_id.
Qed.

Theorem map_add_pf : forall (V W : Normed_Space)(f :Hom V W),map_add V W (Hom_inj f).
Proof.
  intros.
  unfold Hom_inj.
  pose (subtype_h0 (bounded_map V W) (Hom V W) f) as H.
  destruct H.
  tauto.
Qed.

Theorem map_homog_pf : forall (V W : Normed_Space)(f :Hom V W),map_homog V W (Hom_inj f).
Proof.
  intros.
  unfold Hom_inj.
  pose (subtype_h0 (bounded_map V W) (Hom V W) f) as H.
  destruct H.
  tauto.
Qed.

Theorem map_bbd_pf : forall (V W : Normed_Space)(f :Hom V W),map_bdd V W (Hom_inj f).
Proof.
  intros.
  unfold Hom_inj.
  pose (subtype_h0 (bounded_map V W) (Hom V W) f) as H.
  destruct H.
  tauto.
Qed.

Theorem T21g : forall (V W : Normed_Space)(f :Hom V W),Hom_inj f (zero V) = zero W.
Proof.
  intros V W f.
  assert (add W (Hom_inj f (zero V)) (Hom_inj f (zero V)) = Hom_inj f (zero V)).
  rewrite <- map_add_pf.
  rewrite add_id.
  tauto.
  transitivity (add W (neg W (Hom_inj f (zero V))) (Hom_inj f (zero V))).
  apply T21f.
  tauto.
  rewrite add_comm.
  apply add_inv.
Qed.

Theorem T21h : forall (V W : Normed_Space)(f : Hom V W)(x:V) ,Hom_inj f (neg V x) = neg W (Hom_inj f x).
Proof.
  intros V W f x.
  rewrite <- add_id.
  apply T21f.
  rewrite <- map_add_pf.
  rewrite add_inv.
  apply T21g.
Qed.

Theorem T22 : forall (V:Normed_Space)(U:Closed_Subspace V), equivalence (closed_subspace_equiv U).
Proof.
  intros V U.
  unfold equivalence.
  split.
  intros x.
  unfold closed_subspace_equiv.
  exists (zero U).
  rewrite T21g.
  apply add_id.
  split.
  intros x y.
  intros H.
  destruct H.
  unfold closed_subspace_equiv.
  exists (neg U x0).
  rewrite T21h.
  rewrite add_comm.
  rewrite T21f.
  rewrite V9.
  rewrite add_comm.
  symmetry.
  exact H.
  intros x y z.
  intros H1 H2.
  destruct H1.
  destruct H2.
  unfold closed_subspace_equiv.
  exists (add U x0 x1).
  rewrite map_add_pf.
  rewrite add_assoc.
  rewrite H.
  tauto.
Qed.

Definition pre_quotient_space {V:Normed_Space}(U:Closed_Subspace V) := Quotients_Exist V (closed_subspace_equiv U) (T22 _ _).

Print pre_quotient_space.
Theorem T22a {V:Normed_Space}(U:Closed_Subspace V):let W := pre_quotient_space U in
                                                   let equiv := closed_subspace_equiv U in
                                                   (forall x:V, compatible equiv (compose (class equiv W) (add V x))).
Proof.
  intros W.
  intros equiv.
  intros x.
  unfold compatible.
  intros x0 y.
  intros H.
  unfold compose.
  assert (W x0 = W y).
  apply quo_comp.
  tauto.
  apply quo_comp.
  unfold equiv.
  unfold closed_subspace_equiv.
  destruct H.
  exists x1.
  rewrite <- add_assoc.
  apply V8.
  symmetry.
  tauto.
Qed.

Definition pre_quot_add {V:Normed_Space}(U:Closed_Subspace V)(a:V)(b:pre_quotient_space U):pre_quotient_space U.
  pose (W := pre_quotient_space U).
  pose (H := T22a U a).
  pose (equiv := closed_subspace_equiv U).
  pose (pre_f := (compose (class equiv W) (add V a))).
  pose (pre := quo_lift equiv W W pre_f H).
  exact (pre b).
Defined.

Theorem T22b {V:Normed_Space}(U:Closed_Subspace V):let W := pre_quotient_space U in
                                                   let equiv := closed_subspace_equiv U in
                                                   compatible equiv (pre_quot_add U).
Proof.
  intros W.
  intros equiv.
  unfold compatible.
  intros x y.
  intros H.
  unfold pre_quot_add.
  apply Functional_Extensionality_Dep.
  intros x0.
  pose (q := quo_surj equiv W x0).
  destruct q.
  rewrite H0.
  rewrite quo_lift_prop.
  rewrite quo_lift_prop.
  pose (H1 := T22a U x1 x y H).
  unfold compose in H1.
  unfold compose.
  rewrite add_comm.
  rewrite H1.
  rewrite add_comm.
  tauto.
Qed.

Definition quot_add {V:Normed_Space}{U:Closed_Subspace V}(W:=pre_quotient_space U)(a b:W):W.
  pose (equiv := closed_subspace_equiv U).
  pose (H := T22b U).
  pose (pre := quo_lift equiv W (W->W) (pre_quot_add U) H).
  exact (pre a b).
Defined.

(*associativity*)
Theorem T23 {V:Normed_Space}{U:Closed_Subspace V}(W:=pre_quotient_space U)(f:=quot_add) :forall (x y z:W),
    (f (f x y) z = f x (f y z)).
Proof.
  intros x y z.
  pose (equiv := closed_subspace_equiv U).
  pose (h1 :=quo_surj equiv W x).
  destruct h1.
  pose (h1 :=quo_surj equiv W y).
  destruct h1.
  pose (h1 :=quo_surj equiv W z).
  destruct h1.
  assert (pre_quot_add U x0 (W x1) = quot_add x y).
  rewrite H.
  rewrite H0.
  unfold quot_add.
  rewrite (quo_lift_prop).
  tauto.
  rewrite H.
  rewrite H1.
  rewrite H0.
  unfold f.
  unfold quot_add.
  rewrite quo_lift_prop.
  rewrite quo_lift_prop.
  unfold pre_quot_add.
  rewrite quo_lift_prop.
  rewrite quo_lift_prop.
  unfold compose.
  rewrite quo_lift_prop.
  rewrite quo_lift_prop.
  rewrite quo_lift_prop.
  rewrite add_assoc.
  tauto.
Qed.

Theorem T24 {V:Normed_Space}{U:Closed_Subspace V}(W:=pre_quotient_space U)(f:=quot_add) :forall (x y:W), ((f x y) = (f y x)).
Proof.
  intros x y.    
  pose (equiv := closed_subspace_equiv U).
  pose (h1 :=quo_surj equiv W x).
  destruct h1.
  pose (h1 :=quo_surj equiv W y).
  destruct h1.
  rewrite H.
  rewrite H0.
  unfold f.
  unfold quot_add.
  rewrite quo_lift_prop.
  rewrite quo_lift_prop.
  unfold pre_quot_add.
  rewrite quo_lift_prop.
  rewrite quo_lift_prop.
  unfold compose.
  rewrite add_comm.
  congruence.
Qed.
Theorem T24c {V:Normed_Space}(U:Closed_Subspace V):let W := pre_quotient_space U in
                                                   let equiv := closed_subspace_equiv U in
                                                   compatible equiv (compose (class equiv W) (neg V)).
Proof.
  intros W equiv.
  unfold compatible.
  intros x y.
  intros H.
  unfold compose.
  apply quo_comp.
  unfold equiv.
  unfold closed_subspace_equiv.
  destruct H.
  exists (neg U x0).
  rewrite T21h.
  rewrite V10.
  apply V11.  
  assumption.
Qed.

Definition quot_neg {V:Normed_Space}{U:Closed_Subspace V}(W:=pre_quotient_space U)(a:W):W.
  pose (equiv := closed_subspace_equiv U).
  pose (H := T24c U).
  pose (pre := quo_lift equiv W W (compose (class equiv W) (neg V)) H).
  exact (pre a).
Defined.

Definition quot_zero {V:Normed_Space}{U:Closed_Subspace V}
  (W:=pre_quotient_space U)(equiv:=closed_subspace_equiv U):W :=
  class equiv W (zero V).

Theorem T25 {V:Normed_Space}{U:Closed_Subspace V}(W:=pre_quotient_space U)(f:=quot_add)(g:=quot_neg) :
                                               forall (x:W), ((f x (g x)) = quot_zero).
Proof.
  intros.
  pose (equiv := closed_subspace_equiv U).
  destruct (quo_surj equiv W x) as [u].
  rewrite H.  
  unfold f.
  unfold g.
  unfold quot_add.
  rewrite quo_lift_prop.
  unfold pre_quot_add.
  unfold quot_neg.
  rewrite quo_lift_prop.
  unfold compose.
  rewrite quo_lift_prop.
  rewrite add_inv.
  tauto.
Qed.

Theorem T26 {V:Normed_Space}{U:Closed_Subspace V}(W:=pre_quotient_space U)(f:=quot_add) :
                                               forall (x:W), ((f x quot_zero) = x).
Proof.
  intros x.
  pose (equiv := closed_subspace_equiv U).
  destruct (quo_surj equiv W x) as [u].
  rewrite H.  
  unfold f.
  unfold quot_add.
  rewrite quo_lift_prop.
  unfold quot_zero.
  unfold pre_quot_add.
  rewrite quo_lift_prop.
  unfold compose.
  rewrite add_id.
  tauto.
Qed.

Theorem T27 {V:Normed_Space}(U:Closed_Subspace V):let W := pre_quotient_space U in
                                                  let equiv := closed_subspace_equiv U in
                                                  forall (a:R), compatible equiv (compose (class equiv W) (scalar_mul V a)).
Proof.
  intros.
  unfold compatible.
  intros x y.
  intros H.
  unfold compose.
  apply quo_comp.
  unfold equiv.
  destruct H.
  exists (scalar_mul U a x0).
  rewrite map_homog_pf.
  rewrite <- mul_dist2.
  congruence.
Qed.

Definition quot_mul {V:Normed_Space}{U:Closed_Subspace V}(W:=pre_quotient_space U)(a:R):W->W.
  pose (equiv := closed_subspace_equiv U).
  pose (H := T27 U).
  pose (pre := quo_lift equiv W W (compose (class equiv W) (scalar_mul V a)) (H a)).
  exact pre.
Defined.

Theorem T28 {V:Normed_Space}{U:Closed_Subspace V}(W:=pre_quotient_space U)(f:=quot_mul) :forall (x:W)(a b:R),
    (f a (f b x) = f (a*b) x).
Proof.
  intros.
  pose (equiv := closed_subspace_equiv U).
  destruct (quo_surj equiv W x) as [u].
  rewrite H.
  unfold f.
  unfold quot_mul.
  unfold compose.
  rewrite quo_lift_prop.
  rewrite quo_lift_prop.
  rewrite quo_lift_prop.
  rewrite mul_assoc.
  tauto.
Qed.

Theorem T29 {V:Normed_Space}{U:Closed_Subspace V}(W:=pre_quotient_space U)(f:=quot_mul) :forall (x:W),
    (f 1 x = x).
Proof.
  intros.
  pose (equiv := closed_subspace_equiv U).
  destruct (quo_surj equiv W x) as [u].
  rewrite H.
  unfold f.
  unfold quot_mul.
  unfold compose.
  rewrite quo_lift_prop.
  rewrite mul_id.
  tauto.
Qed.

Theorem T30 {V:Normed_Space}{U:Closed_Subspace V}(W:=pre_quotient_space U)(f:=quot_mul)(g:=quot_add) :
  forall (x:W)(a b:R),(f (a+b) x = g (f a x) (f b x)).
Proof.
  intros.
  pose (equiv := closed_subspace_equiv U).
  destruct (quo_surj equiv W x) as [u].
  rewrite H.
  unfold f.
  unfold quot_mul.
  unfold compose.
  rewrite quo_lift_prop.
  rewrite quo_lift_prop.
  rewrite quo_lift_prop.
  unfold g.
  unfold quot_add.
  unfold compose.
  rewrite quo_lift_prop.
  unfold pre_quot_add.
  rewrite quo_lift_prop.
  unfold compose.
  rewrite mul_dist1.
  congruence.
Qed.

Theorem T31 {V:Normed_Space}{U:Closed_Subspace V}(W:=pre_quotient_space U)(f:=quot_mul)(g:=quot_add) :
  forall (x y:W)(a:R),(f a (g x y)  = g (f a x) (f a y)).
Proof.
  intros.
  pose (equiv := closed_subspace_equiv U).
  destruct (quo_surj equiv W x) as [u].
  destruct (quo_surj equiv W y) as [v].
  rewrite H.
  unfold f.
  unfold quot_mul.
  rewrite H0.
  rewrite quo_lift_prop.
  rewrite quo_lift_prop.
  unfold g.
  unfold compose.
  unfold quot_add.
  rewrite quo_lift_prop.
  rewrite quo_lift_prop.
  unfold pre_quot_add.
  rewrite quo_lift_prop.
  rewrite quo_lift_prop.
  unfold compose.
  rewrite quo_lift_prop.
  rewrite mul_dist2.
  trivial.
Qed.

Theorem T31a {V:Normed_Space}{U:Closed_Subspace V}(W:=pre_quotient_space U): forall (x:W),exists s:V, W s = x.
Proof.
  intros.
  pose (equiv := closed_subspace_equiv U).
  destruct (quo_surj equiv W x).
  exists x0.
  symmetry.  
  trivial.
Qed.
Definition quot_norm {V:Normed_Space}{U:Closed_Subspace V}(W:=pre_quotient_space U)(x:W):R.
  exact (dist_to_subset (fun s => W s = x) (zero V) (T31a x)).
Defined.

Theorem T32 {V:Normed_Space}{U:Closed_Subspace V}(W:=pre_quotient_space U)(f:=quot_norm) :
  forall (x:W),f x >= 0.
Proof.
  intros x.
  unfold f.
  unfold quot_norm.
  apply dist_sub_pos.
Qed.

Theorem T32a {V:Normed_Space}(a b c:V): dist (add V a c) (add V b c) = dist a b.
Proof.
  intros.
  unfold dist.
  rewrite <- V10.
  rewrite add_comm.
  rewrite <- add_assoc.
  rewrite (add_comm V b c).
  rewrite (add_assoc V _ c b).
  rewrite (add_comm V (neg V c) c). 
  rewrite add_inv.
  rewrite V5.
  rewrite add_comm.
  trivial.
Qed.


Theorem T32b {V:Normed_Space}{U:Closed_Subspace V}(W:=pre_quotient_space U)(x:W)(sub:=fun s=> W s =x): 
  forall (y:V), closure sub y <-> sub y.
Proof.
  intros.
  split.
  intros H.
  unfold closure in H.
  pose (subspace_closure V U).
  pose (equiv := closed_subspace_equiv U).
  destruct (quo_surj equiv W x) as [u].
  pose (i (add V y (neg V u))).
  destruct i0.
  assert (closure (int_closed_subspace V U) (add V y (neg V u))).
  unfold closure.
  intros eps.
  pose (H eps).
  destruct e.
  destruct H3.
  exists (add V x0 (neg V u)).
  split.
  unfold int_closed_subspace.
  unfold sub in H3.
  rewrite H0 in H3.
  pose (quo_comp_rev equiv W _ _ H3).
  unfold equiv in e.
  unfold closed_subspace_equiv in e.
  destruct e.
  exists (neg U x1).
  rewrite T21h.
  rewrite <- V11.   
  rewrite V9.
  rewrite <- (V8 V x0).
  rewrite H5.
  rewrite <- V10.  
  rewrite add_assoc.
  rewrite add_inv.
  rewrite V5.
  apply V9.
  rewrite T32a.
  trivial.
  unfold sub.
  pose (H1 H3).
  unfold int_closed_subspace in i0.
  rewrite H0.
  apply quo_comp.
  unfold equiv.
  unfold closed_subspace_equiv.
  destruct i0.
  exists (neg U x0).
  rewrite T21h.
  rewrite H4.
  rewrite <- V10.
  rewrite add_assoc.
  rewrite add_inv.
  rewrite V9.
  rewrite V5.
  trivial.
  intros H.
  unfold closure.
  intros eps.
  exists y.
  split.
  trivial.
  unfold dist.
  rewrite add_inv.
  rewrite V2.
  destruct eps.
  tauto.
Qed.
  
Theorem T33 {V:Normed_Space}{U:Closed_Subspace V}(W:=pre_quotient_space U)(f:=quot_norm) :
  forall (x:W),f x = 0 -> x=quot_zero.
Proof.
  intros.
  unfold f in H.
  unfold quot_norm in H.
  pose (T20e _ _ _ H).
  pose (sub := fun s : V => (pre_quotient_space U) s = x).
  assert (closure sub = sub).
  apply Predicate_Extensionality.
  apply T32b.
  fold sub in c.
  rewrite H0 in c.
  unfold sub in c.
  pose (equiv := closed_subspace_equiv U).
  destruct (quo_surj equiv W x) as [u].
  rewrite H1.
  symmetry.
  unfold quot_zero.
  congruence.
Qed.

Theorem T33a {V:Normed_Space}(A : V -> Prop)(x:V)(f : exists (y:V),A y) :
 forall y:V, (A y) -> dist_to_subset A x f <= dist x y.
Proof.
  intros.
  unfold dist_to_subset.
  pose (pdist_to_subset A x f).
  fold s.
  destruct s.
  destruct a.
  destruct H0.
  unfold is_lower_bound in H0.
  apply H0.
  unfold pre_dist_to_subset.
  exists y.
  tauto.
Qed.

Theorem T34 {V:Normed_Space}{U:Closed_Subspace V}
  (W:=pre_quotient_space U)(f:=quot_norm)(g:=quot_add):
  forall (x y :W),f (g x y) <= f x + f y.
Proof.
  intros.
  pose (equiv := closed_subspace_equiv U).
  destruct (quo_surj equiv W x) as [u].
  destruct (quo_surj equiv W y) as [v].
  assert (forall (a b :V), (W a = x) -> (W b = y) ->
                           (norm V a)+(norm V b) >= f (g x y)).
  intros a b.
  intros.
  refine (Rge_trans ((norm V a)+(norm V b)) (norm V (add V a b)) (f (g x y)) _ _ ).
  apply Rle_ge.
  apply norm_add.
  unfold f.
  unfold quot_norm.
  apply Rle_ge.
  assert (norm V (add V a b) = dist (zero V) (add V a b)).
  unfold dist.
  rewrite V4.
  trivial.
  rewrite H3.
  apply T33a.
  rewrite <- H1.
  rewrite <- H2.
  unfold g.
  unfold quot_add.
  rewrite quo_lift_prop.
  unfold pre_quot_add.
  rewrite quo_lift_prop.
  unfold compose.  
  trivial.
  assert (forall eps:posreal,f (g x y) < f x + f y + eps).
  intros eps.
  destruct eps.
  assert (pos = pos/2 +pos/2).  
  field.
  simpl.
  rewrite H2.
  assert (exists s:V,W s = x /\ norm V s < (f x + pos/2)). 
  unfold f.
  unfold quot_norm.
  unfold dist_to_subset.
  pose (sub := (fun s0 : V => (pre_quotient_space U) s0 = x)).
  pose (r:=pdist_to_subset sub (zero V)).
  pose (quo_surj equiv W x).
  unfold sub in r.
  pose (r1 := r (T31a x)).
  fold r.
  fold r1.
  destruct r1.
  destruct a.
  pose (H4 (x0+pos/2)).
  assert (x0+pos/2>x0).
  rewrite <- Rplus_0_r.
  apply Rplus_lt_compat_l.
  apply Rmult_gt_0_compat.
  trivial.
  apply Rinv_0_lt_compat.  
  apply R7.
  pose (H4 _ H5).
  destruct e1.
  fold sub in H6.
  destruct H6.
  destruct H6.
  destruct H6.
  exists x2.
  split.
  unfold sub in H6.
  trivial.
  unfold dist in H8.
  rewrite V4 in H8.
  rewrite H8.
  trivial.
  assert (exists s:V,W s = y /\ norm V s < (f y + pos/2)). 
  unfold f.
  unfold quot_norm.
  unfold dist_to_subset.
  pose (sub := (fun s0 : V => (pre_quotient_space U) s0 = y)).
  pose (r:=pdist_to_subset sub (zero V)).
  pose (quo_surj equiv W y).
  pose (r1 := r (T31a y)).
  unfold sub in r.
  fold r.
  fold r1.
  destruct r1.
  destruct a.
  pose (H5 (x0+pos/2)).
  assert (x0+pos/2>x0).
  rewrite <- Rplus_0_r.
  apply Rplus_lt_compat_l.
  apply Rmult_gt_0_compat.
  trivial.
  apply Rinv_0_lt_compat.  
  apply R7.
  pose (H5 _ H6).
  destruct e1.
  fold sub in H6.
  destruct H7.
  destruct H7.
  destruct H7.
  exists x2.
  split.
  unfold sub in H6.
  trivial.
  unfold dist in H9.
  rewrite V4 in H9.
  rewrite H9.
  trivial.
  destruct H3,H4.
  destruct H3,H4.
  apply (Rle_lt_trans _ (norm V x0 + norm V x1) _).  
  pose (H1 _ _ H3 H4).
  apply Rge_le.
  trivial.
  rewrite Rplus_assoc.
  rewrite <- (Rplus_assoc (f y) (pos/2) (pos/2)).
  rewrite (Rplus_comm (f y +pos/2)).
  rewrite <- Rplus_assoc.
  apply Rplus_gt_compat.
  apply Rlt_gt.
  trivial.
  apply Rlt_gt.
  trivial.
  apply Rge_le.
  apply R9.
  intros p.
  pose (H2 p).
  apply Rlt_gt.
  trivial.
Qed.

Theorem T35 {V:Normed_Space}{U:Closed_Subspace V}
  (W:=pre_quotient_space U)(f:=quot_norm)(g:=quot_mul):
  forall (x:W)(a:R),f (g a x) = (Rabs a)*f x.
Proof.
  intros.
  pose (equiv := closed_subspace_equiv U).
  destruct (quo_surj equiv W x) as [u].
  rewrite H.
  unfold g.
  unfold quot_mul.
  rewrite quo_lift_prop.
  unfold compose.
  unfold f.
  unfold quot_norm.