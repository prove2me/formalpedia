-- Prove2me | Theorems.Thm_WeightedCacheParameters_log_bankArg_lower_bounds
-- name    : WeightedCacheParameters.log_bankArg_lower_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:55:20.189794+00:00
-- url     : https://prove2.me/theorems/a62536c7-ce8f-48c3-9b33-8c9eabc13c66
-- title:
--   Weighted Cache Parameters: log bank Arg lower bounds
-- statement:
--   The Weighted Cache Parameters construction uses the log bank Arg lower bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Parameters.lean#L230-L237
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Parameters.lean#L230-L237

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

theorem WeightedCacheParameters.log_bankArg_lower_bounds :
    (194413244396031453 / 1000000000000000000 : ℝ) ≤ Real.log ((151824763140233107 / 125000000000000000 : ℝ)) ∧ Real.log ((151824763140233107 / 125000000000000000 : ℝ)) ≤ (38882648879206291 / 200000000000000000 : ℝ) := by sorry
