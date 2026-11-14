-- Prove2me | Theorems.Thm_ProbabilityTheory_lt_jumpCount_iff
-- name    : ProbabilityTheory.lt_jumpCount_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:14:41.235743+00:00
-- url     : https://prove2.me/theorems/110151f9-7d15-43bb-8525-0f224e8c7c63
-- title:
--   LeanLevy: ProbabilityTheory.lt_jumpCount_iff
-- statement:
--   The defining characterization of the jump count: `n` jumps have occurred by time `t` Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4//home/willr/projects/Prove2Me/scratch/leanlevy_bulk_20261027/source/LeanLevy/Processes/PiecewisePath.lean#L60

import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Definitions.Def_LeanLevy_Processes_Cadlag
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

theorem ProbabilityTheory.lt_jumpCount_iff : ∀ {T : Nat → Real},
  @StrictMono Nat Real Nat.instPreorder Real.instPreorder T →
    @Filter.Tendsto Nat Real T (@Filter.atTop Nat Nat.instPreorder) (@Filter.atTop Real Real.instPreorder) →
      ∀ (n : Nat) (t : Real),
        Iff (@LT.lt Nat instLTNat n (ProbabilityTheory.jumpCount T t)) (@LE.le Real Real.instLE (T n) t) := by sorry
