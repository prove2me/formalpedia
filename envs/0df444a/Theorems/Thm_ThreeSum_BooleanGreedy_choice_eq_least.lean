-- Prove2me | Theorems.Thm_ThreeSum_BooleanGreedy_choice_eq_least
-- name    : ThreeSum.BooleanGreedy.choice_eq_least
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-14T14:43:06.279989+00:00
-- url     : https://prove2.me/theorems/9e539207-bc31-476a-b3c7-be5da467dab2
-- title:
--   Greedy row selection equals the scan of negated scores
-- statement:
--   Let $M:\mathbb N^2\to\mathbb N$ have $R>0$ rows and $C$ columns, with $M_{ij}\le1$ for valid row and column indices. Let $a_t(j)$ indicate whether column $j$ remains uncovered after $t$ greedy steps, and define the row score $s_t(i)=\sum_{j<C}M_{ij}a_t(j)$. Then
--
--   $$
--   \operatorname{choice}(M,R,C,t)=\operatorname{least}_{i<R}\bigl(-s_t(i)\bigr).
--   $$
--
--   The right side is the left-to-right integer minimum scan, retaining the earliest index on ties. This identifies the finite greedy covering choice with the score computation and scan used by the implementation.
-- source:
--   https://github.com/c0ldzy17/three-sum-lean/blob/2b639655e07421b9ac743de9090459bab473a7c0/Submission/ThreeSum/BooleanGreedy.lean#L69-L95

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
namespace Light
end Light
namespace ThreeSum.LightMinimum
end ThreeSum.LightMinimum

theorem ThreeSum.BooleanGreedy.choice_eq_least : ∀ {matrix : Nat → Nat → Nat} {rows cols : Nat}
  (hrows : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) rows)
  (hmatrix :
    ∀ (i : Nat),
      @LT.lt.{0} Nat instLTNat i rows →
        ∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j cols →
            @LE.le.{0} Nat instLENat (matrix i j) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (t : Nat),
  @Eq.{1} Nat (ThreeSum.BooleanGreedy.choice matrix rows cols t)
    (ThreeSum.LightMinimum.least
      (fun (i : Nat) =>
        @Neg.neg.{0} Int Int.instNegInt
          (@Nat.cast.{0} Int instNatCastInt
            (ThreeSum.LightCoverScores.score matrix (ThreeSum.BooleanGreedy.active matrix rows cols t) cols i)))
      rows) := by
  sorry
