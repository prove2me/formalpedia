-- Prove2me | Theorems.Thm_WeightedCacheParameters_e1ae71d_log_queryArg2_lower_bounds
-- name    : WeightedCacheParameters_e1ae71d.log_queryArg2_lower_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:29.901572+00:00
-- url     : https://prove2.me/theorems/5e82dd8b-f3e7-4dac-b182-14a9e724e393
-- title:
--   log_queryArg2_lower_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L327-L334
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L327-L334

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

theorem WeightedCacheParameters_e1ae71d.log_queryArg2_lower_bounds :
    (19387293186940463 / 250000000000000000 : ℝ) ≤ Real.log ((540317684481267861 / 500000000000000000 : ℝ)) ∧ Real.log ((540317684481267861 / 500000000000000000 : ℝ)) ≤ (38774586373880927 / 500000000000000000 : ℝ) := by sorry
