-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFastProgramResources_scanFree_eq
-- name    : ThreeSum.WeightedGlobalFastProgramResources.scanFree_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:56:29.917145+00:00
-- url     : https://prove2.me/theorems/ae01a7bf-c5cd-497f-af07-0cb32bc67674
-- title:
--   Weighted Global Fast Program Resources: scan Free eq
-- statement:
--   The Weighted Global Fast Program Resources construction uses the scan Free eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean#L24-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean#L24-L27

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_Submission_ThreeSum_ThreeSumColorDriverResources
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalFastProgramResources
open Light LightWeightedGlobalFastProgram LightWeightedGlobalFastProgramProof
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalFastProgramResources.scanFree_eq (M b p K κ n U free : ℕ) :
    scanFree M b p K κ n free=free+(WeightedGlobalGlobalPreludeResources.need M b p K κ n U).cells := by sorry
