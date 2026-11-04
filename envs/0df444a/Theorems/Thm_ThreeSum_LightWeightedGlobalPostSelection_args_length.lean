-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPostSelection_args_length
-- name    : ThreeSum.LightWeightedGlobalPostSelection.args_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:16:22.387868+00:00
-- url     : https://prove2.me/theorems/2f205dce-8b97-4796-aea0-4a32a7fbc2ef
-- title:
--   Light Weighted Global Post Selection: args length
-- statement:
--   The Light Weighted Global Post Selection construction uses the args length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPostSelectionClosed.lean#L51-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPostSelectionClosed.lean#L51-L53

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelection
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelectionClosed
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_args_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_args_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.args_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.args_length


set_option autoImplicit false
noncomputable section
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000
open ThreeSum ThreeSum.LightWeightedGlobalPostSelection
open Light TernaryMomentSchedule

theorem ThreeSum.LightWeightedGlobalPostSelection.args_length {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (c : LightOriginalSurvivorPair.Layout) (scratch matrix : ℕ) :
    (args S c scratch matrix).length = 148 := by sorry

attribute [defeq] ThreeSum.LightWeightedGlobalPostSelection.args_length
