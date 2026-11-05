-- Prove2me | Theorems.Thm_WeightedCacheParameters_e1ae71d_log_queryArg1_lower_bounds
-- name    : WeightedCacheParameters_e1ae71d.log_queryArg1_lower_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:23.068213+00:00
-- url     : https://prove2.me/theorems/3088b920-2852-47d4-aa59-b50975324421
-- title:
--   log_queryArg1_lower_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L281-L288
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L281-L288

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

theorem WeightedCacheParameters_e1ae71d.log_queryArg1_lower_bounds :
    (14515179898819027 / 200000000000000000 : ℝ) ≤ Real.log ((537637207888609881 / 500000000000000000 : ℝ)) ∧ Real.log ((537637207888609881 / 500000000000000000 : ℝ)) ≤ (72575899494095137 / 1000000000000000000 : ℝ) := by sorry
