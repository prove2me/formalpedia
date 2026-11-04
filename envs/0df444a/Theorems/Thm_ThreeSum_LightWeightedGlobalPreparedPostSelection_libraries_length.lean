-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPreparedPostSelection_libraries_length
-- name    : ThreeSum.LightWeightedGlobalPreparedPostSelection.libraries_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:31:25.074818+00:00
-- url     : https://prove2.me/theorems/97549f05-5a1e-419a-939a-9ecd600149ad
-- title:
--   Light Weighted Global Prepared Post Selection: libraries length
-- statement:
--   The Light Weighted Global Prepared Post Selection construction uses the libraries length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPreparedPostSelection.lean#L205-L207
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPreparedPostSelection.lean#L205-L207

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_LightTernaryFinalPreparation
import Definitions.Def_Submission_Weighted_Global_LightTernaryPostSelectionClosed
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedGlobalPostSelection_libraries_length
import Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_libraries_length
attribute [local simp] ThreeSum.LightTernarySourceCountHost.libraries_length
attribute [local simp] ThreeSum.LightWeightedGlobalPostSelection.libraries_length
attribute [local simp] ThreeSum.LightWeightedSourceCountHost.libraries_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPreparedPostSelection
open Light LightSubsetAddress LightOriginalSurvivorPair LightOriginalCollisionCleanup
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPreparedPostSelection.libraries_length {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ) :
    (libraries S H).length = 139*(TernaryMomentSchedule.channels (2*H+1)).length+24 := by sorry
