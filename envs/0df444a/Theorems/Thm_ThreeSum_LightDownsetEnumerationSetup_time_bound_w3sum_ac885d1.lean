-- Prove2me | Theorems.Thm_ThreeSum_LightDownsetEnumerationSetup_time_bound_w3sum_ac885d1
-- name    : ThreeSum.LightDownsetEnumerationSetup.time_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:06:16.38547+00:00
-- url     : https://prove2.me/theorems/6cdc06b4-129c-4f1a-937f-90fb61f44bfa
-- title:
--   Light Downset Enumeration Setup: time bound
-- statement:
--   The Light Downset Enumeration Setup construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetEnumerationSetup.lean#L80-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetEnumerationSetup.lean#L80-L95

import Definitions.Def_Submission_ThreeSum_LightDownsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumerationSetup
import Definitions.Def_WeightedCache3SUM_Alias_f1b1ba0c94539568
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetEnumerationSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDownsetEnumerationSetup.time_bound_w3sum_ac885d1 {L cut : ℕ} (hcut : cut ≤ L) :
    time L cut ≤ 1200*(L+1)^2*(downsetCap L cut+1) := by sorry
