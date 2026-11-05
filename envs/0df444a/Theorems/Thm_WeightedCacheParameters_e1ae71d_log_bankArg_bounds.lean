-- Prove2me | Theorems.Thm_WeightedCacheParameters_e1ae71d_log_bankArg_bounds
-- name    : WeightedCacheParameters_e1ae71d.log_bankArg_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:33.522177+00:00
-- url     : https://prove2.me/theorems/00119ee0-c873-4261-99b2-aab3a4e4f837
-- title:
--   log_bankArg_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L263-L269
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L263-L269

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

theorem WeightedCacheParameters_e1ae71d.log_bankArg_bounds :
    (194416086704412431 / 1000000000000000000 : ℝ) ≤ Real.log bankArg ∧ Real.log bankArg ≤ (194416086704412433 / 1000000000000000000 : ℝ) := by sorry
