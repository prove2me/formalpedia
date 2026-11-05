-- Prove2me | Theorems.Thm_WeightedCacheParameters_e1ae71d_log_bankArg_lower_bounds
-- name    : WeightedCacheParameters_e1ae71d.log_bankArg_lower_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:21.046623+00:00
-- url     : https://prove2.me/theorems/8cf2adee-58c9-49d0-91ff-928b476e8f6b
-- title:
--   log_bankArg_lower_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L235-L242
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L235-L242

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
set_option autoImplicit false
noncomputable section
open WeightedCacheParameters_e1ae71d
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096

theorem WeightedCacheParameters_e1ae71d.log_bankArg_lower_bounds :
    (194416086704412431 / 1000000000000000000 : ℝ) ≤ Real.log ((242920311477828953 / 200000000000000000 : ℝ)) ∧ Real.log ((242920311477828953 / 200000000000000000 : ℝ)) ≤ (194416086704412433 / 1000000000000000000 : ℝ) := by sorry
