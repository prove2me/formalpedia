-- Prove2me | Theorems.Thm_ThreeSum_LightBlockChildren_time_bound
-- name    : ThreeSum.LightBlockChildren.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:02:57.187208+00:00
-- url     : https://prove2.me/theorems/119e4a3b-96b6-4bd4-8b8a-de7f0db4f841
-- title:
--   Light Block Children: time bound
-- statement:
--   The Light Block Children construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildren.lean#L177-L182
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockChildren.lean#L177-L182

import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightBlockChildren
import Theorems.Thm_ThreeSum_LightQueryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightQueryWeights_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockChildren
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostMasks
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBlockChildren.time_bound {W c h : ℕ} (hc : c ≤ W) :
    time W c h ≤ 1600*(W+1)^2*(c.choose h+1) := by sorry
