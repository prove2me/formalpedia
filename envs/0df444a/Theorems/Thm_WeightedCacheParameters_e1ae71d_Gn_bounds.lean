-- Prove2me | Theorems.Thm_WeightedCacheParameters_e1ae71d_Gn_bounds
-- name    : WeightedCacheParameters_e1ae71d.Gn_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:14.996126+00:00
-- url     : https://prove2.me/theorems/65e64459-0eef-4392-ae53-e7d2a5057060
-- title:
--   Gn_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L380-L384
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L380-L384

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

theorem WeightedCacheParameters_e1ae71d.Gn_bounds : (71075103071640423 / 500000000000000000 : ℝ) ≤ Gn ∧ Gn ≤ (142150206143280847 / 1000000000000000000 : ℝ) := by sorry
