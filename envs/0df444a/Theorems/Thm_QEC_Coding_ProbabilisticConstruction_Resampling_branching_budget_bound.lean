-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_branching_budget_bound
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.branching_budget_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:22:04.425081+00:00
-- url     : https://prove2.me/theorems/338139b7-d946-4305-960b-16ad7fe30c5e
-- title:
--   Resampling: branching budget bound
-- statement:
--   The finite branching recurrence is bounded by the explicit asymmetric budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessTrees.lean#L103-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessTrees.lean#L103-L134

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.branching_budget_bound (p x : I → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1)
    (hcrit : ∀ i, p i ≤ x i * ∏ j ∈ G.neighborFinset i, (1 - x j)) (i : I) :
    p i * ∏ j ∈ closedNeighbors G i, (1 + resamplingBudget x j) ≤
      resamplingBudget x i := by sorry
