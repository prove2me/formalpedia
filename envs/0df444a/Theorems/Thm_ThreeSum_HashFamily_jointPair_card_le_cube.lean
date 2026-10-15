-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_jointPair_card_le_cube
-- name    : ThreeSum.HashFamily.jointPair_card_le_cube
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:48:04.574414+00:00
-- url     : https://prove2.me/theorems/c5e51d42-0782-43e6-a881-093b1f1c8b2f
-- title:
--   Two distinct cross-class edges impose at least three hash constraints
-- statement:
--   Let $\alpha$ be a finite coordinate set and $K$ a finite field of size $q$, with decidable equality. Let $\mathcal W=K^{\alpha\times\{0,1\}}$, and define $H_w(z)=\sum_{i\in\alpha}w(i,z_i)$. Let $(s,t)$ and $(u,v)$ be distinct ordered word pairs with $\{s,u\}\cap\{t,v\}=\varnothing$. For targets $a,b\in K$, write $E_{s,t}=\{w:H_w(s)=a,\ H_w(t)=b\}$. Then
--
--   $$q^3|E_{s,t}\cap E_{u,v}|\le|\mathcal W|.$$
--
--   Endpoints within the same class may coincide. This joint-event bound provides the cubic denominator used for potentially dependent edge pairs in the second moment.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/HashFamily.lean#L306-L334

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
import Theorems.Thm_ThreeSum_HashFamily_hashMap_surjective
import Theorems.Thm_ThreeSum_HashFamily_linear_fiber_card
import Theorems.Thm_ThreeSum_HashFamily_three_relation


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_2

theorem ThreeSum.HashFamily.jointPair_card_le_cube : ∀ {α : Type u_1} {K : Type u_2} [inst : Fintype.{u_1} α] [inst_1 : DecidableEq.{u_1 + 1} α] [inst_2 : Field.{u_2} K]
  [inst_3 : Fintype.{u_2} K] [inst_4 : DecidableEq.{u_2 + 1} K] {s t u v : α → Bool}
  (hst : @Ne.{u_1 + 1} (α → Bool) s t) (hsv : @Ne.{u_1 + 1} (α → Bool) s v) (htu : @Ne.{u_1 + 1} (α → Bool) t u)
  (huv : @Ne.{u_1 + 1} (α → Bool) u v)
  (hpair :
    @Ne.{u_1 + 1} (Prod.{u_1, u_1} (α → Bool) (α → Bool)) (@Prod.mk.{u_1, u_1} (α → Bool) (α → Bool) s t)
      (@Prod.mk.{u_1, u_1} (α → Bool) (α → Bool) u v))
  (a b : K),
  @LE.le.{0} Nat instLENat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@Fintype.card.{u_2} K inst_3) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@Finset.card.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
        (@Inter.inter.{max u_2 u_1} (Finset.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K))
          (@Finset.instInter.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K) fun (a b : Prod.{u_1, 0} α Bool → K) =>
            @Fintype.decidablePiFintype.{u_2, u_1} (Prod.{u_1, 0} α Bool) (fun (a : Prod.{u_1, 0} α Bool) => K)
              (fun (a : Prod.{u_1, 0} α Bool) => inst_4) (@instFintypeProd.{u_1, 0} α Bool inst Bool.fintype) a b)
          (@ThreeSum.HashFamily.pairEvent.{u_1, u_2} α K inst inst_1 inst_2 inst_3 inst_4 s t a b)
          (@ThreeSum.HashFamily.pairEvent.{u_1, u_2} α K inst inst_1 inst_2 inst_3 inst_4 u v a b))))
    (@Fintype.card.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
      (@Pi.instFintype.{u_1, u_2} (Prod.{u_1, 0} α Bool) (fun (a : Prod.{u_1, 0} α Bool) => K)
        (fun (a b : Prod.{u_1, 0} α Bool) => @instDecidableEqProd.{u_1, 0} α Bool inst_1 instDecidableEqBool a b)
        (@instFintypeProd.{u_1, 0} α Bool inst Bool.fintype) fun (a : Prod.{u_1, 0} α Bool) => inst_3)) := by
  sorry
