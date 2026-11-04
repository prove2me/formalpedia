-- Prove2me | Theorems.Thm_ThreeSum_ThreeSumColorDriverResources_color_of_ok
-- name    : ThreeSum.ThreeSumColorDriverResources.color_of_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:05:37.949142+00:00
-- url     : https://prove2.me/theorems/1f5b8042-a14f-495e-bb93-23792834d6e2
-- title:
--   Three Sum Color Driver Resources: color of ok
-- statement:
--   The Three Sum Color Driver Resources construction uses the color of ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ThreeSumColorDriverResources.lean#L42-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ThreeSumColorDriverResources.lean#L42-L49

import Definitions.Def_Submission_ThreeSum_LightThreeSumColorDriver
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
import Definitions.Def_Submission_ThreeSum_ThreeSumColorDriverResources
import Theorems.Thm_ThreeSum_SharedReportingBankHeader_Stored_row

set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumColorDriverResources
open Light Scales StageBounds ArithmeticStageBounds LightColorParametersCosts ColorParameters
set_option maxHeartbeats 2000000
set_option maxRecDepth 14000

theorem ThreeSum.ThreeSumColorDriverResources.color_of_ok {lim : Limits} {colorNeed : ℕ→ℕ→Need} {n U row d dd : ℕ}
    (H : (need colorNeed n U).Ok lim row d)
    (hd : dd+(colorNeed n U).depth≤lim.depth) :
    (colorNeed n U).Ok lim (row+6) dd := by sorry
