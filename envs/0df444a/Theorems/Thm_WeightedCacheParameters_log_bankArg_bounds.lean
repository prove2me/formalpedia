-- Prove2me | Theorems.Thm_WeightedCacheParameters_log_bankArg_bounds
-- name    : WeightedCacheParameters.log_bankArg_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:55:24.817097+00:00
-- url     : https://prove2.me/theorems/743d6c90-5fd0-49a2-8f6e-1135212e3cd9
-- title:
--   Weighted Cache Parameters: log bank Arg bounds
-- statement:
--   The Weighted Cache Parameters construction uses the log bank Arg bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Parameters.lean#L258-L264
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Parameters.lean#L258-L264

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

theorem WeightedCacheParameters.log_bankArg_bounds :
    (194413244396031453 / 1000000000000000000 : ℝ) ≤ Real.log bankArg ∧ Real.log bankArg ≤ (6075413887375983 / 31250000000000000 : ℝ) := by sorry
