-- Prove2me | Theorems.Thm_WeightedCacheParameters_log_alpha0_bounds
-- name    : WeightedCacheParameters.log_alpha0_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:54:39.065211+00:00
-- url     : https://prove2.me/theorems/67ee7e89-1432-4576-91d9-f86bd8cd6865
-- title:
--   Weighted Cache Parameters: log alpha0 bounds
-- statement:
--   The Weighted Cache Parameters construction uses the log alpha0 bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Parameters.lean#L116-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Parameters.lean#L116-L123

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_Weighted_Parameters
set_option autoImplicit false
noncomputable section
open WeightedCacheParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

theorem WeightedCacheParameters.log_alpha0_bounds :
    (-104083450637781559 / 1000000000000000000 : ℝ) ≤ Real.log (alpha0) ∧ Real.log (alpha0) ≤ (-26020862659445389 / 250000000000000000 : ℝ) := by sorry
