-- Prove2me | Theorems.Thm_ThreeSum_LightCacheEnumeration_time_bound
-- name    : ThreeSum.LightCacheEnumeration.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:35:19.983274+00:00
-- url     : https://prove2.me/theorems/07540f75-bed0-406a-a467-822bfbb6a068
-- title:
--   Light Cache Enumeration: time bound
-- statement:
--   The Light Cache Enumeration construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightEnumeration.lean#L104-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightEnumeration.lean#L104-L106

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_LightEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightCacheEnumeration
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Light ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightCacheEnumeration.time_bound (N T : ℕ) :
    time N T ≤ 300*((N+1)*(codes N T).length) := by sorry
