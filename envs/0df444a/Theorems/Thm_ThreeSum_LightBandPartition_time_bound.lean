-- Prove2me | Theorems.Thm_ThreeSum_LightBandPartition_time_bound
-- name    : ThreeSum.LightBandPartition.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:20:45.978219+00:00
-- url     : https://prove2.me/theorems/420fd4ae-4d21-48aa-8e20-a8e0b2a38244
-- title:
--   Light Band Partition: time bound
-- statement:
--   The Light Band Partition construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPartition.lean#L193-L198
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandPartition.lean#L193-L198

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPartition
open Light ThreeSum.BandPartition
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandPartition.time_bound (n g : ℕ) : time n g ≤ 200*n+200 := by sorry
