-- Prove2me | Theorems.Thm_ThreeSum_LightZetaStages_time_bound_w3sum_ac885d1
-- name    : ThreeSum.LightZetaStages.time_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:30.169314+00:00
-- url     : https://prove2.me/theorems/7bc93f8b-d255-400f-916f-359e198dbb2a
-- title:
--   Light Zeta Stages: time bound
-- statement:
--   The Light Zeta Stages construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaStages.lean#L211-L230
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaStages.lean#L211-L230

import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b

set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaStages
open Light ThreeSum.SubsetAddress ThreeSum.SubsetStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightZetaStages.time_bound_w3sum_ac885d1 {L cut : ℕ} (hcut : cut ≤ L) :
    time L cut ≤ 6000*(L+1)^4*(downsetCap L cut+1) := by sorry
