-- Prove2me | Theorems.Thm_WeightedCacheParameters_e1ae71d_log_alpha1_bounds
-- name    : WeightedCacheParameters_e1ae71d.log_alpha1_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:25.812148+00:00
-- url     : https://prove2.me/theorems/78723a71-b0d5-4183-b570-bc696ee12006
-- title:
--   log_alpha1_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L140-L147
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L140-L147

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

theorem WeightedCacheParameters_e1ae71d.log_alpha1_bounds :
    (-2418109533236553567 / 1000000000000000000 : ℝ) ≤ Real.log (alpha1) ∧ Real.log (alpha1) ≤ (-2418109533236553561 / 1000000000000000000 : ℝ) := by sorry
