-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFastProgramResources_global_ok
-- name    : ThreeSum.WeightedGlobalFastProgramResources.global_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:57:10.850291+00:00
-- url     : https://prove2.me/theorems/176daf10-d2a5-4620-8507-815a685bbbcb
-- title:
--   Weighted Global Fast Program Resources: global ok
-- statement:
--   The Weighted Global Fast Program Resources construction uses the global ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean#L29-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean#L29-L33

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

theorem ThreeSum.WeightedGlobalFastProgramResources.global_ok {M b p K κ n U free depth : ℕ} {colorNeed : ℕ→ℕ→Need} {lim : Limits}
    (H : (need M b p K κ colorNeed n U).Ok lim free depth) :
    (WeightedGlobalGlobalPreludeResources.need M b p K κ n U).Ok lim free (depth+1) := by sorry
