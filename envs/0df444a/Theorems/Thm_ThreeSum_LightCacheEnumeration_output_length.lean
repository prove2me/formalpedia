-- Prove2me | Theorems.Thm_ThreeSum_LightCacheEnumeration_output_length
-- name    : ThreeSum.LightCacheEnumeration.output_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:35:39.143644+00:00
-- url     : https://prove2.me/theorems/194b3500-f867-4abb-94c5-e8ca69b310f5
-- title:
--   Light Cache Enumeration: output length
-- statement:
--   The Light Cache Enumeration construction uses the output length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightEnumeration.lean#L23-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightEnumeration.lean#L23-L24

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_LightEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightCacheEnumeration
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
open Light ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightCacheEnumeration.output_length (N T pref : ℕ) :
    (output N T pref).length = (codes N T).length := by sorry
