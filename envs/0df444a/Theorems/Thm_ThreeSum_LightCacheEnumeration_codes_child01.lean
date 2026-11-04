-- Prove2me | Theorems.Thm_ThreeSum_LightCacheEnumeration_codes_child01
-- name    : ThreeSum.LightCacheEnumeration.codes_child01
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:24:38.352429+00:00
-- url     : https://prove2.me/theorems/369ac143-ac4b-4ef6-b92b-2e31f6c7f785
-- title:
--   Light Cache Enumeration: codes child01
-- statement:
--   The Light Cache Enumeration construction uses the codes child01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightEnumeration.lean#L76-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightEnumeration.lean#L76-L80

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

theorem ThreeSum.LightCacheEnumeration.codes_child01 {T : ℕ} (hT : 512≤T) (N : ℕ) :
    (codes N T).length+(codes N (T-512)).length ≤ (codes (N+1) T).length := by sorry
