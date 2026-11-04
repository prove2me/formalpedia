-- Prove2me | Theorems.Thm_ThreeSum_LightCacheEnumeration_output_succ_mid
-- name    : ThreeSum.LightCacheEnumeration.output_succ_mid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:23:48.965669+00:00
-- url     : https://prove2.me/theorems/37513030-31c4-4131-94ca-b75f31481b92
-- title:
--   Light Cache Enumeration: output succ mid
-- statement:
--   The Light Cache Enumeration construction uses the output succ mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightEnumeration.lean#L39-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightEnumeration.lean#L39-L42

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_LightEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightCacheEnumeration
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Light ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightCacheEnumeration.output_succ_mid {T : ℕ} (hT : 512 ≤ T) (hT' : T < 1025) (N pref : ℕ) :
    output (N+1) T pref = output N T pref ++ output N (T-512) (pref+4^N) := by sorry
