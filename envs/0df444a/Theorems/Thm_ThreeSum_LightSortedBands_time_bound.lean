-- Prove2me | Theorems.Thm_ThreeSum_LightSortedBands_time_bound
-- name    : ThreeSum.LightSortedBands.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:42:17.520643+00:00
-- url     : https://prove2.me/theorems/001cc9dd-c92e-464a-ab6e-c1caad108346
-- title:
--   Light Sorted Bands: time bound
-- statement:
--   The Light Sorted Bands construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSortedBands.lean#L236-L239
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSortedBands.lean#L236-L239

import Definitions.Def_Submission_ThreeSum_LightNormalize
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_LightSortedBands
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightBandPartition_time_bound
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound
import Theorems.Thm_ThreeSum_LightNormalize_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightSortedBands
open Light ThreeSum.BandPartition
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSortedBands.time_bound (n : ℕ) : time n ≤ 700*(n+1)*(Nat.clog 2 n+1) := by sorry
