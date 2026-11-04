-- Prove2me | Theorems.Thm_ThreeSum_ThreeSumColorDriverResources_allocation_eq
-- name    : ThreeSum.ThreeSumColorDriverResources.allocation_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:05:52.912017+00:00
-- url     : https://prove2.me/theorems/ef8dc382-16b2-4784-91dc-1bf48c852845
-- title:
--   Three Sum Color Driver Resources: allocation eq
-- statement:
--   The Three Sum Color Driver Resources construction uses the allocation eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ThreeSumColorDriverResources.lean#L63-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ThreeSumColorDriverResources.lean#L63-L68

import Definitions.Def_Submission_ThreeSum_LightThreeSumColorDriver
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
import Definitions.Def_Submission_ThreeSum_ThreeSumColorDriverResources
set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumColorDriverResources
open Light Scales StageBounds ArithmeticStageBounds LightColorParametersCosts ColorParameters
set_option maxHeartbeats 2000000
set_option maxRecDepth 14000

theorem ThreeSum.ThreeSumColorDriverResources.allocation_eq (colorNeed : ℕ→ℕ→Need) (n U : ℕ) :
    (fullNeed colorNeed n U).cells=
      max (ThreeSumParameterResources.need n U).cells (25+(colorNeed n U).cells) := by sorry
