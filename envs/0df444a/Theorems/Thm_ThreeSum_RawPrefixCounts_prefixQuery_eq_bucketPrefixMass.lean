-- Prove2me | Theorems.Thm_ThreeSum_RawPrefixCounts_prefixQuery_eq_bucketPrefixMass
-- name    : ThreeSum.RawPrefixCounts.prefixQuery_eq_bucketPrefixMass
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T15:26:23.577726+00:00
-- url     : https://prove2.me/theorems/c0cc7132-edda-49b6-869a-21d9873962c5
-- title:
--   Raw prefix counts equal guarded sums of bucket products
-- statement:
--   Let $A,B,C$ be finite indexed sets in finite types with decidable equality, with integer values $a,b,c$. Fix natural $h,J,k$, integers $P,d$, a wanted label $w=(i,\lambda,q)$, and any prefix list $u$; here $\lambda\in\{-1,0,1\}$ is the lift and $q$ the global output. Let $\mathcal T$ contain the retained choice tuples with output $q$ and first $k$ partition entries equal to $u$.
--
--   For global modulus $M$, let $L_t$ count $j\in B$ with $M\mid b(j)\bmod P-\operatorname{tupleLeft}(t)$, and $R_t$ count $j\in C$ with $M\mid c(j)\bmod P+d-\operatorname{tupleRight}(t)$. The raw prefix query satisfies
--   $$
--   Q_w(k,u)=\mathbf1_{\{i\in A,\ M\mid a(i)\bmod P+\lambda P+d-\operatorname{globalKey}(q)\}}
--   \sum_{t\in\mathcal T}L_tR_t.
--   $$
--   This factors each guarded raw count into independently counted original-index buckets.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/RawPrefixCounts.lean#L105-L142

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Radix_mem_representations


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting

universe u_1 u_2 u_3

theorem ThreeSum.RawPrefixCounts.prefixQuery_eq_bucketPrefixMass : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β] [Fintype.{u_3} γ]
  [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {h J : Nat} (P d : Int)
  (A : Finset.{u_1} α) (B : Finset.{u_2} β) (C : Finset.{u_3} γ) (a : α → Int) (b : β → Int) (c : γ → Int)
  (w : ThreeSum.RawReporting.Wanted.{u_1} h J α) (k : Nat)
  (pre :
    List.{0}
      (Finset.{0}
        (Fin
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))),
  @Eq.{1} Nat
    (@ThreeSum.RawReporting.prefixQuery.{u_1, u_2, u_3} α β γ inst h J
      (@ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J P d
        (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
          (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
          (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
          (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
          (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
            (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
        a b c)
      w k pre)
    (@ThreeSum.RawPrefixCounts.bucketPrefixMass.{u_1, u_2, u_3} α β γ inst h J P d A B C a b c w k pre) := by
  sorry
