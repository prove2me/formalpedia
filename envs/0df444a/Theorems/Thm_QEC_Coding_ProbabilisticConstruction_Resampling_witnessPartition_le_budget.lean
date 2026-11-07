-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_le_budget
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_le_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:45:47.556204+00:00
-- url     : https://prove2.me/theorems/39ff3153-9a21-43cb-bec5-900d461163f0
-- title:
--   Resampling: witness Partition le budget
-- statement:
--   Proper witness trees have a uniformly bounded total probability weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessTrees.lean#L137-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/WitnessTrees.lean#L137-L149

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_le_budget (p x : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hcrit : ∀ i, p i ≤ x i * ∏ j ∈ G.neighborFinset i, (1 - x j))
    (h : ℕ) (i : I) : witnessPartition G p h i ≤ resamplingBudget x i := by sorry
