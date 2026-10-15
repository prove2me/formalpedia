-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_raw_second_moment
-- name    : ThreeSum.HashFamily.raw_second_moment
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:18:50.149523+00:00
-- url     : https://prove2.me/theorems/78cf530b-3fd5-4be2-8dad-7107bcfe2135
-- title:
--   Raw second-moment bound for the concrete one-hot hash family
-- statement:
--   Let $\alpha,E$ be finite types and $K$ a finite field of size $q$. Assign each edge $e\in E$ binary endpoint words $\ell_e,r_e:\alpha\to\{0,1\}$. Assume the ordered endpoint pairs are distinct and $\ell_e\ne r_f$ for every $e,f$. For each $e$, suppose at most $B$ edges $f$ share its left word, share its right word, or have the same coordinatewise equality mask $[\ell_e(i)=r_e(i)]$. For $a,b\in K$ and every weight assignment $w:\alpha\times\{0,1\}\to K$, let $X_w$ count edges with $\sum_iw(i,\ell_e(i))=a$ and $\sum_iw(i,r_e(i))=b$. Writing $m=|E|$ and $\mathcal W=K^{\alpha\times\{0,1\}}$, one has
--
--   $$
--   q^4\sum_{w\in\mathcal W}X_w^2
--   \le |\mathcal W|\bigl(mq^2+m^2+mBq\bigr).
--   $$
--
--   This controls the second moment by explicitly counting exceptional endpoint dependencies in the actual hash family.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/HashFamily.lean#L521-L560

import Definitions.Def_ThreeSum1962Source_Bundle01
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum_HashFamily_four_relation_of_mask_ne
import Theorems.Thm_ThreeSum_HashFamily_hashMap_surjective
import Theorems.Thm_ThreeSum_HashFamily_jointPair_card_le_cube
import Theorems.Thm_ThreeSum_HashFamily_linear_fiber_card
import Theorems.Thm_ThreeSum_HashFamily_sum_incidenceCount_sq


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_2 u_3

theorem ThreeSum.HashFamily.raw_second_moment : ∀ {α : Type u_1} {K : Type u_2} {E : Type u_3} [inst : Fintype.{u_3} E] [DecidableEq.{u_3 + 1} E]
  [inst_2 : Fintype.{u_1} α] [inst_3 : DecidableEq.{u_1 + 1} α] [inst_4 : Field.{u_2} K] [inst_5 : Fintype.{u_2} K]
  [inst_6 : DecidableEq.{u_2 + 1} K] (left right : E → α → Bool)
  (hinj :
    @Function.Injective.{u_3 + 1, u_1 + 1} E (Prod.{u_1, u_1} (α → Bool) (α → Bool)) fun (e : E) =>
      @Prod.mk.{u_1, u_1} (α → Bool) (α → Bool) (left e) (right e))
  (hcross : ∀ (e f : E), @Ne.{u_1 + 1} (α → Bool) (left e) (right f)) (B : Nat)
  (hB :
    ∀ (e : E),
      @LE.le.{0} Nat instLENat
        (@Finset.card.{u_3} E (@ThreeSum.HashFamily.badPartners.{u_1, u_3} α E inst inst_2 left right e)) B)
  (a b : K),
  @LE.le.{0} Nat instLENat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@Fintype.card.{u_2} K inst_5) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (∑ w : Prod.{u_1, 0} α Bool → K,
        @HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@ThreeSum.HashFamily.incidenceCount.{max u_2 u_1, u_3} (Prod.{u_1, 0} α Bool → K) E inst
            (fun (a b : Prod.{u_1, 0} α Bool → K) =>
              @Fintype.decidablePiFintype.{u_2, u_1} (Prod.{u_1, 0} α Bool) (fun (a : Prod.{u_1, 0} α Bool) => K)
                (fun (a : Prod.{u_1, 0} α Bool) => inst_6) (@instFintypeProd.{u_1, 0} α Bool inst_2 Bool.fintype) a b)
            (fun (e : E) =>
              @ThreeSum.HashFamily.pairEvent.{u_1, u_2} α K inst_2 inst_3 inst_4 inst_5 inst_6 (left e) (right e) a b)
            w)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@Fintype.card.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
        (@Pi.instFintype.{u_1, u_2} (Prod.{u_1, 0} α Bool) (fun (a : Prod.{u_1, 0} α Bool) => K)
          (fun (a b : Prod.{u_1, 0} α Bool) => @instDecidableEqProd.{u_1, 0} α Bool inst_3 instDecidableEqBool a b)
          (@instFintypeProd.{u_1, 0} α Bool inst_2 Bool.fintype) fun (a : Prod.{u_1, 0} α Bool) => inst_5))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{u_3} E inst)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@Fintype.card.{u_2} K inst_5) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@Fintype.card.{u_3} E inst) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{u_3} E inst) B)
          (@Fintype.card.{u_2} K inst_5)))) := by
  sorry
