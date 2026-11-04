-- Prove2me | Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
-- name    : ThreeSum.LightDownsetAddress.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:36:41.789565+00:00
-- url     : https://prove2.me/theorems/2a16f3f8-3878-4d58-a9c0-099f19788d0d
-- title:
--   Light Downset Address: time bound
-- statement:
--   The Light Downset Address construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetAddress.lean#L89-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetAddress.lean#L89-L92

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_LightDownsetAddress
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetAddress
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDownsetAddress.time_bound (L : ℕ) : time L ≤ 1300*(L+1)^2 := by sorry
