-- Prove2me | Theorems.Thm_ThreeSum_LightBoxStages_time_bound_w3sum_ac885d1
-- name    : ThreeSum.LightBoxStages.time_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:35.761943+00:00
-- url     : https://prove2.me/theorems/a646a7bf-ba74-4cb6-bb02-67c592eb46b9
-- title:
--   Light Box Stages: time bound
-- statement:
--   The Light Box Stages construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxStages.lean#L215-L234
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxStages.lean#L215-L234

import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_LightBoxStages
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b

set_option autoImplicit false
open ThreeSum ThreeSum.LightBoxStages
open Light ThreeSum.SubsetAddress ThreeSum.BoxStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBoxStages.time_bound_w3sum_ac885d1 {L cut : ℕ} (hcut : cut ≤ L) :
    time L cut ≤ 6000*(L+1)^4*(downsetCap L cut+1) := by sorry
