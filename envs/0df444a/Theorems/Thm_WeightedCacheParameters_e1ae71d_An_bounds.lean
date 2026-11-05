-- Prove2me | Theorems.Thm_WeightedCacheParameters_e1ae71d_An_bounds
-- name    : WeightedCacheParameters_e1ae71d.An_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:16.397024+00:00
-- url     : https://prove2.me/theorems/6da15eb8-6063-499c-8315-3903ead939ca
-- title:
--   An_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L372-L377
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L372-L377

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

theorem WeightedCacheParameters_e1ae71d.An_bounds : (5537922463388799 / 15625000000000000 : ℝ) ≤ An ∧ An ≤ (354427037656883141 / 1000000000000000000 : ℝ) := by sorry
