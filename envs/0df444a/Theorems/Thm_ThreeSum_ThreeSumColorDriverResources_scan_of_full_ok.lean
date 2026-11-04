-- Prove2me | Theorems.Thm_ThreeSum_ThreeSumColorDriverResources_scan_of_full_ok
-- name    : ThreeSum.ThreeSumColorDriverResources.scan_of_full_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:09:35.192881+00:00
-- url     : https://prove2.me/theorems/5c77b158-fc5e-436f-a9e5-4dccd87155b4
-- title:
--   Three Sum Color Driver Resources: scan of full ok
-- statement:
--   The Three Sum Color Driver Resources construction uses the scan of full ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ThreeSumColorDriverResources.lean#L57-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ThreeSumColorDriverResources.lean#L57-L61

import Definitions.Def_Submission_ThreeSum_LightThreeSumColorDriver
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
import Definitions.Def_Submission_ThreeSum_ThreeSumColorDriverResources
set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumColorDriverResources
open Light Scales StageBounds ArithmeticStageBounds LightColorParametersCosts ColorParameters
set_option maxHeartbeats 2000000
set_option maxRecDepth 14000

theorem ThreeSum.ThreeSumColorDriverResources.scan_of_full_ok {lim : Limits} {colorNeed : ℕ→ℕ→Need} {n U free d : ℕ}
    (H : (fullNeed colorNeed n U).Ok lim free d) :
    (need colorNeed n U).Ok lim (free+19) (d+1) := by sorry
