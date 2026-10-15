-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_loadedPairMass_bound
-- name    : ThreeSum.HashFamily.loadedPairMass_bound
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:48:01.200177+00:00
-- url     : https://prove2.me/theorems/c8f3ee29-c1dc-44b9-bab3-78e773ac79cb
-- title:
--   Conditional hash-bucket load has a finite mass bound
-- statement:
--   Let $\alpha$ be finite, let $K$ be a finite field of size $q$, and use all coefficient functions $\mathcal W=K^{\alpha\times\{0,1\}}$ with one-hot hash $H_w$. Fix distinct Boolean words $s,t$, targets $a,b\in K$, and a finite vertex set $V$ with $t\notin V$. Set $E=\{w:H_w(s)=a,\ H_w(t)=b\}$ and $B_w=|\{u\in V:H_w(u)=a\}|$. Then
--
--   $$q^3\sum_{w\in E}B_w\le(q+|V|)|\mathcal W|.$$
--
--   There is no requirement that $s$ belong to $V$. This controls bucket load under a fixed endpoint-pair event, supporting the separable trimming estimate.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/HashFamily.lean#L609-L656

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

theorem ThreeSum.HashFamily.loadedPairMass_bound : ∀ {α : Type u_1} {K : Type u_2} [inst : Fintype.{u_1} α] [inst_1 : DecidableEq.{u_1 + 1} α] [inst_2 : Field.{u_2} K]
  [inst_3 : Fintype.{u_2} K] [inst_4 : DecidableEq.{u_2 + 1} K] {s t : α → Bool} (hst : @Ne.{u_1 + 1} (α → Bool) s t)
  (a b : K) (vertices : Finset.{u_1} (α → Bool))
  (hcross :
    ∀ (u : α → Bool),
      @Membership.mem.{u_1, u_1} (α → Bool) (Finset.{u_1} (α → Bool))
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} (α → Bool)) (α → Bool)
            (@Finset.instSetLike.{u_1} (α → Bool)))
          vertices u →
        @Ne.{u_1 + 1} (α → Bool) u t),
  @LE.le.{0} Nat instLENat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@Fintype.card.{u_2} K inst_3) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@ThreeSum.HashFamily.loadedPairMass.{u_1, u_2} α K inst inst_1 inst_2 inst_3 inst_4 s t a b vertices))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fintype.card.{u_2} K inst_3)
        (@Finset.card.{u_1} (α → Bool) vertices))
      (@Fintype.card.{max u_1 u_2} (Prod.{u_1, 0} α Bool → K)
        (@Pi.instFintype.{u_1, u_2} (Prod.{u_1, 0} α Bool) (fun (a : Prod.{u_1, 0} α Bool) => K)
          (fun (a b : Prod.{u_1, 0} α Bool) => @instDecidableEqProd.{u_1, 0} α Bool inst_1 instDecidableEqBool a b)
          (@instFintypeProd.{u_1, 0} α Bool inst Bool.fintype) fun (a : Prod.{u_1, 0} α Bool) => inst_3))) := by
  sorry
