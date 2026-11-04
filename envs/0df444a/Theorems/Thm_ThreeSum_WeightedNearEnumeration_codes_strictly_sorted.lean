-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_strictly_sorted
-- name    : ThreeSum.WeightedNearEnumeration.codes_strictly_sorted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:24.321376+00:00
-- url     : https://prove2.me/theorems/26c54b29-3888-4e3c-a2f8-4182000a3601
-- title:
--   Weighted Near Enumeration: codes strictly sorted
-- statement:
--   The Weighted Near Enumeration construction uses the codes strictly sorted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L158-L180
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L158-L180

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_strictly_sorted
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_strictly_sorted

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedNearEnumeration.codes_strictly_sorted (qs : List ℕ) (D : ℕ) (hq : ∀ q ∈ qs, q < 3) :
    (codes qs D).Pairwise (· < ·) := by sorry
