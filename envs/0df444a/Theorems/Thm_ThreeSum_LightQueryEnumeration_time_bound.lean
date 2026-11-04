-- Prove2me | Theorems.Thm_ThreeSum_LightQueryEnumeration_time_bound
-- name    : ThreeSum.LightQueryEnumeration.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:56:41.509706+00:00
-- url     : https://prove2.me/theorems/eec03ee7-59ba-428f-850b-69ef4b39a75e
-- title:
--   Light Query Enumeration: time bound
-- statement:
--   The Light Query Enumeration construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryEnumeration.lean#L92-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryEnumeration.lean#L92-L100

import Definitions.Def_Submission_ThreeSum_LightQueryWeights
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Theorems.Thm_ThreeSum_LightQueryWeights_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress QueryCoordinates
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightQueryEnumeration.time_bound {W c t : ℕ} (hc : c ≤ W) :
    time W c t ≤ 1400*(W+1)^2*(c.choose t+1) := by sorry
