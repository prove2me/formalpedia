-- Prove2me | Theorems.Thm_ThreeSum_LightDownsetEnumeration_time_bound_w3sum_ac885d1
-- name    : ThreeSum.LightDownsetEnumeration.time_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:31:34.915726+00:00
-- url     : https://prove2.me/theorems/f0c1beeb-8219-4f70-8e09-a52f6003f0e4
-- title:
--   Light Downset Enumeration: time bound
-- statement:
--   The Light Downset Enumeration construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetEnumeration.lean#L145-L160
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetEnumeration.lean#L145-L160

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDownsetEnumeration.time_bound_w3sum_ac885d1 {L cut : ℕ} (hcut : cut ≤ L) :
    time L cut ≤ 1000*(L+1)^2*(downsetCap L cut+1) := by sorry
