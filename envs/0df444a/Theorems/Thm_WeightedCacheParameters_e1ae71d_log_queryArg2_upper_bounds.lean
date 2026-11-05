-- Prove2me | Theorems.Thm_WeightedCacheParameters_e1ae71d_log_queryArg2_upper_bounds
-- name    : WeightedCacheParameters_e1ae71d.log_queryArg2_upper_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:26.693133+00:00
-- url     : https://prove2.me/theorems/49e6a36f-fd57-4f3d-9211-5cd953247e8d
-- title:
--   log_queryArg2_upper_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L346-L353
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L346-L353

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

theorem WeightedCacheParameters_e1ae71d.log_queryArg2_upper_bounds :
    (77549172747761853 / 1000000000000000000 : ℝ) ≤ Real.log ((1080635368962535723 / 1000000000000000000 : ℝ)) ∧ Real.log ((1080635368962535723 / 1000000000000000000 : ℝ)) ≤ (15509834549552371 / 200000000000000000 : ℝ) := by sorry
