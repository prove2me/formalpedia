-- Prove2me | Theorems.Thm_WeightedCacheParameters_e1ae71d_Hn_bounds
-- name    : WeightedCacheParameters_e1ae71d.Hn_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:20.491204+00:00
-- url     : https://prove2.me/theorems/558da07b-c0ff-450e-8c7c-c9919f96689c
-- title:
--   Hn_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L364-L369
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L364-L369

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

theorem WeightedCacheParameters_e1ae71d.Hn_bounds : (141139799958643803 / 250000000000000000 : ℝ) ≤ Hn ∧ Hn ≤ (564559199834575217 / 1000000000000000000 : ℝ) := by sorry
