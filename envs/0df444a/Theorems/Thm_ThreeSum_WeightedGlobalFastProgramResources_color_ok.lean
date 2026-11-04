-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalFastProgramResources_color_ok
-- name    : ThreeSum.WeightedGlobalFastProgramResources.color_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:59:25.894298+00:00
-- url     : https://prove2.me/theorems/4d39758e-f3b0-4d6c-b512-7a081314ea4a
-- title:
--   Weighted Global Fast Program Resources: color ok
-- statement:
--   The Weighted Global Fast Program Resources construction uses the color ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean#L43-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryFastProgramResources.lean#L43-L47

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

theorem ThreeSum.WeightedGlobalFastProgramResources.color_ok {M b p K κ n U free depth dd : ℕ} {colorNeed : ℕ→ℕ→Need} {lim : Limits}
    (H : (need M b p K κ colorNeed n U).Ok lim free depth)
    (hd : dd+(colorNeed n U).depth≤lim.depth) :
    (colorNeed n U).Ok lim (scanFree M b p K κ n free+6) dd := by sorry
