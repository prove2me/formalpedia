-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_length
-- name    : ThreeSum.WeightedNearEnumeration.codes_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:03.273831+00:00
-- url     : https://prove2.me/theorems/6c4ba30c-1a96-4374-b5e8-56b6188eac49
-- title:
--   Weighted Near Enumeration: codes length
-- statement:
--   The Weighted Near Enumeration construction uses the codes length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L148-L149
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L148-L149

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.WeightedAddresses.codes_length


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedNearEnumeration.codes_length (qs : List ℕ) (D : ℕ) :
    (codes qs D).length = (words qs D).length := by sorry
