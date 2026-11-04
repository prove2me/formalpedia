-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPreparedPostSelection_args_length
-- name    : ThreeSum.LightWeightedGlobalPreparedPostSelection.args_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:28:32.657841+00:00
-- url     : https://prove2.me/theorems/90bc4c8e-5193-4d6c-8009-f0894423217f
-- title:
--   Light Weighted Global Prepared Post Selection: args length
-- statement:
--   The Light Weighted Global Prepared Post Selection construction uses the args length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPreparedPostSelection.lean#L213-L214
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPreparedPostSelection.lean#L213-L214

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelectionClosed
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_args_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalPostSelection_args_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_args_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.args_length
attribute [local simp] ThreeSum.LightWeightedGlobalPostSelection.args_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.args_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPreparedPostSelection
open Light LightSubsetAddress LightOriginalSurvivorPair LightOriginalCollisionCleanup
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPreparedPostSelection.args_length {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (c : Layout) (scratch matrix : ℕ) : (args S c scratch matrix).length = 148 := by sorry

attribute [defeq] ThreeSum.LightWeightedGlobalPreparedPostSelection.args_length
