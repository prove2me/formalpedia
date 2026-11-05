-- Prove2me | Theorems.Thm_WeightedCacheParameters_e1ae71d_log_queryArg1_upper_bounds
-- name    : WeightedCacheParameters_e1ae71d.log_queryArg1_upper_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:26.182192+00:00
-- url     : https://prove2.me/theorems/0a0b29fc-1f4a-4756-bdc3-a2224d41f7bc
-- title:
--   log_queryArg1_upper_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L300-L307
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L300-L307

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

theorem WeightedCacheParameters_e1ae71d.log_queryArg1_upper_bounds :
    (2267996859190473 / 31250000000000000 : ℝ) ≤ Real.log ((1075274415777219763 / 1000000000000000000 : ℝ)) ∧ Real.log ((1075274415777219763 / 1000000000000000000 : ℝ)) ≤ (36287949747047569 / 500000000000000000 : ℝ) := by sorry
