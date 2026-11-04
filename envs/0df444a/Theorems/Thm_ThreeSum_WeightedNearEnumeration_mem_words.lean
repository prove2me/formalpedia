-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_words
-- name    : ThreeSum.WeightedNearEnumeration.mem_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:33:53.204926+00:00
-- url     : https://prove2.me/theorems/a4f3d04a-6a4b-447a-a344-02aff937edf0
-- title:
--   Weighted Near Enumeration: mem words
-- statement:
--   The Weighted Near Enumeration construction uses the mem words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L41-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L41-L54

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_words

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedNearEnumeration.mem_words (qs rs : List ℕ) (D : ℕ) : rs ∈ words qs D ↔ Admitted qs rs D := by sorry
