-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixFinish_step_eq
-- name    : ThreeSum.LightWeightedGlobalPrefixFinish.step_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:56:22.93019+00:00
-- url     : https://prove2.me/theorems/ca9fad35-4423-4d87-8fa6-2c9c4fefcc9c
-- title:
--   Light Weighted Global Prefix Finish: step eq
-- statement:
--   The Light Weighted Global Prefix Finish construction uses the step eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixFinish.lean#L27-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryPrefixFinish.lean#L27-L28

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFullController
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixProgramLibrary
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixFinish
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalPrefixFinish
open Light LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory
open LightWeightedGlobalPrefixLoop
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalPrefixFinish.step_eq : stepBody = (
    .call 196 [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16] 19 ;; body) := by sorry
