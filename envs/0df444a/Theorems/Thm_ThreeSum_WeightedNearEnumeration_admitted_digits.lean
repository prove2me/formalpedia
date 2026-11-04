-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearEnumeration_admitted_digits
-- name    : ThreeSum.WeightedNearEnumeration.admitted_digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:06.3392+00:00
-- url     : https://prove2.me/theorems/bf970730-f5ba-468a-ae9a-8a74552121b9
-- title:
--   Weighted Near Enumeration: admitted digits
-- statement:
--   The Weighted Near Enumeration construction uses the admitted digits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L116-L127
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L116-L127

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedNearEnumeration.admitted_digits {qs rs : List ℕ} {D : ℕ}
    (hq : ∀ q ∈ qs, q < 3) (h : Admitted qs rs D) : ∀ r ∈ rs, r < 3 := by sorry
