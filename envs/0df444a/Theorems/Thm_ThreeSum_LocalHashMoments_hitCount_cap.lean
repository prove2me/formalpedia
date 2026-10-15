-- Prove2me | Theorems.Thm_ThreeSum_LocalHashMoments_hitCount_cap
-- name    : ThreeSum.LocalHashMoments.hitCount_cap
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:27:11.823392+00:00
-- url     : https://prove2.me/theorems/6b8567fc-0cc7-4c02-8722-8a67018f5cc6
-- title:
--   A retained hash target has at most the square of the bucket cap representations
-- statement:
--   Let $K$ be a finite field, let $L,h,B\in\mathbb N$, and assign weights $w:\{0,\ldots,L-1\}\times\{0,1\}\to K$. The local graph has ordered pairs of disjoint $h$-subsets as edges, with the left word equal to one on its subset and the right word equal to zero on its subset. A word $s$ has hash $\sum_i w(i,s(i))$. Fix any target $(a,b)\in K^2$. Count edges whose endpoint hashes are $a,b$ and whose corresponding left and right hash buckets both contain at most $B$ vertices. This retained hit count satisfies
--
--   $$
--   \operatorname{hits}_{L,h,B}(w;a,b)\le B^2.
--   $$
--
--   The two target values may be equal, and no positivity or separation hypothesis on $L,h,B$ is required.
--
--   This supplies a pointwise representation cap for every retained target, complementing the averaged hash-moment estimates.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LocalHashMoments.lean#L165-L197

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
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
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph

universe u_1

theorem ThreeSum.LocalHashMoments.hitCount_cap : ∀ {K : Type u_1} [inst : Field.{u_1} K] [inst_1 : Fintype.{u_1} K] [inst_2 : DecidableEq.{u_1 + 1} K] {L h : Nat}
  (B : Nat) (w : ThreeSum.LocalHashMoments.Weight.{u_1} L K) (target : Prod.{u_1, u_1} K K),
  @LE.le.{0} Nat instLENat (@ThreeSum.LocalHashMoments.hitCount.{u_1} K inst inst_1 inst_2 L h B w target)
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) B
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  sorry
