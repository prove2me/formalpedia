-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearEnumeration_words_nonempty
-- name    : ThreeSum.WeightedNearEnumeration.words_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:59.873199+00:00
-- url     : https://prove2.me/theorems/b25e2472-2a5b-44ce-b135-01cc38066327
-- title:
--   Weighted Near Enumeration: words nonempty
-- statement:
--   The Weighted Near Enumeration construction uses the words nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L61-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L61-L62

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_TernaryEnumeration_words_nonempty
import Theorems.Thm_ThreeSum_WeightedEnumeration_words_nonempty

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedNearEnumeration.words_nonempty (qs : List ℕ) (D : ℕ) : 0 < (words qs D).length := by sorry
