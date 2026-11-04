-- Prove2me | Theorems.Thm_ThreeSum_ThreeSumParameterResources_resources_of_ok
-- name    : ThreeSum.ThreeSumParameterResources.resources_of_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:21:32.173061+00:00
-- url     : https://prove2.me/theorems/2d91cfcd-1dc2-4259-89d6-f82f96bed690
-- title:
--   Three Sum Parameter Resources: resources of ok
-- statement:
--   The Three Sum Parameter Resources construction uses the resources of ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ThreeSumParameterResources.lean#L108-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ThreeSumParameterResources.lean#L108-L116

import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_resources_of_ok

set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumParameterResources
open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds
set_option maxHeartbeats 2200000
set_option maxRecDepth 14000

theorem ThreeSum.ThreeSumParameterResources.resources_of_ok {lim : Limits} {n U dst d : ℕ}
    (hok : (need n U).Ok lim dst d) :
    LightParameterInit.space (work dst) n ≤ lim.space ∧
    (LightParameterInit.word n : ℤ) ≤ lim.word ∧
      d+512*LightParameterInit.half n+6 ≤ lim.depth := by sorry
