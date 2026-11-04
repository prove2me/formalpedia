-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_time_bound
-- name    : ThreeSum.LightWeightedNearEnumeration.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:41:10.317123+00:00
-- url     : https://prove2.me/theorems/99e5cbbe-e551-4015-85ba-b84d95b31179
-- title:
--   Light Weighted Near Enumeration: time bound
-- statement:
--   The Light Weighted Near Enumeration construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightNearEnumeration.lean#L207-L209
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightNearEnumeration.lean#L207-L209

import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_LightNearEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedNearEnumeration
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.WeightedNearEnumeration
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedNearEnumeration.time_bound (qs : List ℕ) (D : ℕ) :
    time qs D ≤ 900*((qs.length+1)*(words qs D).length) := by sorry
