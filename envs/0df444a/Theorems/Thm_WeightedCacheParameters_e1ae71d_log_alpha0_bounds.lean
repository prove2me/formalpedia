-- Prove2me | Theorems.Thm_WeightedCacheParameters_e1ae71d_log_alpha0_bounds
-- name    : WeightedCacheParameters_e1ae71d.log_alpha0_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:22.776288+00:00
-- url     : https://prove2.me/theorems/1ea317b5-42dd-4862-b8e7-f65cc6bbed17
-- title:
--   log_alpha0_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L121-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L121-L128

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

theorem WeightedCacheParameters_e1ae71d.log_alpha0_bounds :
    (-104088228038551707 / 1000000000000000000 : ℝ) ≤ Real.log (alpha0) ∧ Real.log (alpha0) ≤ (-13011028504818963 / 125000000000000000 : ℝ) := by sorry
