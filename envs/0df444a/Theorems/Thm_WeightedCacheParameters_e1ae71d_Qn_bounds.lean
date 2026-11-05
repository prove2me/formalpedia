-- Prove2me | Theorems.Thm_WeightedCacheParameters_e1ae71d_Qn_bounds
-- name    : WeightedCacheParameters_e1ae71d.Qn_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:17.356816+00:00
-- url     : https://prove2.me/theorems/6e823004-1192-4851-9c6c-b245658909ca
-- title:
--   Qn_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L394-L399
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Parameters.lean#L394-L399

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

theorem WeightedCacheParameters_e1ae71d.Qn_bounds : (3035725394303803 / 62500000000000000 : ℝ) ≤ Qn ∧ Qn ≤ (6071450788607613 / 125000000000000000 : ℝ) := by sorry
