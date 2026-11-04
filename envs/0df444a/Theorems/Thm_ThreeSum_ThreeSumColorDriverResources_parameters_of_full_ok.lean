-- Prove2me | Theorems.Thm_ThreeSum_ThreeSumColorDriverResources_parameters_of_full_ok
-- name    : ThreeSum.ThreeSumColorDriverResources.parameters_of_full_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:06:06.793701+00:00
-- url     : https://prove2.me/theorems/8b326411-e6e0-40fd-93af-aeebadbbcfa6
-- title:
--   Three Sum Color Driver Resources: parameters of full ok
-- statement:
--   The Three Sum Color Driver Resources construction uses the parameters of full ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ThreeSumColorDriverResources.lean#L51-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ThreeSumColorDriverResources.lean#L51-L55

import Definitions.Def_Submission_ThreeSum_LightThreeSumColorDriver
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
import Definitions.Def_Submission_ThreeSum_ThreeSumColorDriverResources
set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumColorDriverResources
open Light Scales StageBounds ArithmeticStageBounds LightColorParametersCosts ColorParameters
set_option maxHeartbeats 2000000
set_option maxRecDepth 14000

theorem ThreeSum.ThreeSumColorDriverResources.parameters_of_full_ok {lim : Limits} {colorNeed : ℕ→ℕ→Need} {n U free d : ℕ}
    (H : (fullNeed colorNeed n U).Ok lim free d) :
    (ThreeSumParameterResources.need n U).Ok lim free (d+1) := by sorry
