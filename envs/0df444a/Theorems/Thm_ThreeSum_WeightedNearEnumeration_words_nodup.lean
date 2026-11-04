-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearEnumeration_words_nodup
-- name    : ThreeSum.WeightedNearEnumeration.words_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:02.767206+00:00
-- url     : https://prove2.me/theorems/ab221410-cd27-4280-820e-95ede2ccf046
-- title:
--   Weighted Near Enumeration: words nodup
-- statement:
--   The Weighted Near Enumeration construction uses the words nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L182-L186
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L182-L186

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedNearEnumeration.words_nodup (qs : List ℕ) (D : ℕ) (hq : ∀ q ∈ qs, q < 3) :
    (words qs D).Nodup := by sorry
