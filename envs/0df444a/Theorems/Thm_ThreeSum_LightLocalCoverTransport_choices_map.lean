-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverTransport_choices_map
-- name    : ThreeSum.LightLocalCoverTransport.choices_map
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:43:06.054485+00:00
-- url     : https://prove2.me/theorems/6925c627-a0fe-4e08-9295-855b167bac1c
-- title:
--   Relabeling preserves the complete greedy choice list
-- statement:
--   Let $\Omega$ be an inhabited candidate type and $U$ a target type with decidable equality. Let $M:\mathbb N^2\to\mathbb N$, $c:\mathbb N\to\Omega$, and $u:\mathbb N\to U$, with a decidable covering relation. Fix $R>0$ rows and $C$ columns. Assume $u$ is injective below $C$ and, for every row index $i$ and $j<C$, $M_{ij}=1$ exactly when $c(i)$ covers $u(j)$. For every number of rounds $t$,
--
--   $$
--   \operatorname{map}(c,\operatorname{BooleanChoices}(M,R,C,t))
--   =\operatorname{GreedyChoices}([c(0),\ldots,c(R-1)],\{u(j):j<C\},t).
--   $$
--
--   Both greedy procedures break ties by the given list order. Candidate labels may repeat, and matrix entries need not be bounded by one; only equality to one defines coverage. The identity preserves the whole ordered schedule.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/LightLocalCoverTransport.lean#L17-L77

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_IndexedGreedy_argmax_range


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LightMinimum
end ThreeSum.LightMinimum

universe u_1 u_2

theorem ThreeSum.LightLocalCoverTransport.choices_map : ∀ {Ω : Type u_1} {U : Type u_2} [inst : Inhabited.{u_1 + 1} Ω] [inst_1 : DecidableEq.{u_2 + 1} U]
  (matrix : Nat → Nat → Nat) (candidate : Nat → Ω) (target : Nat → U) (covers : Ω → U → Prop)
  [inst_2 : @DecidableRel.{u_1 + 1, u_2 + 1} Ω U covers] {rows cols : Nat}
  (hrows : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) rows)
  (hinj :
    @Set.InjOn.{0, u_2} Nat U target
      (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat) (Finset.range cols)))
  (hcover :
    ∀ (i j : Nat),
      @LT.lt.{0} Nat instLTNat j cols →
        Iff (ThreeSum.BooleanGreedy.covers matrix i j) (covers (candidate i) (target j)))
  (rounds : Nat),
  @Eq.{u_1 + 1} (List.{u_1} Ω)
    (@List.map.{0, u_1} Nat Ω candidate (ThreeSum.BooleanGreedy.choices matrix rows cols rounds))
    (@ThreeSum.Cover.greedyChoices.{u_1, u_2} Ω U inst (@List.map.{0, u_1} Nat Ω candidate (List.range rows)) covers
      inst_2 (@Finset.image.{0, u_2} Nat U inst_1 target (Finset.range cols)) rounds) := by
  sorry
