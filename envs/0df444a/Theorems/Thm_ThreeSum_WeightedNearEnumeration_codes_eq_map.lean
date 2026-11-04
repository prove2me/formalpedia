-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_eq_map
-- name    : ThreeSum.WeightedNearEnumeration.codes_eq_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:09.923208+00:00
-- url     : https://prove2.me/theorems/40c27fab-a873-408f-8bf2-383ae87d0a7b
-- title:
--   Weighted Near Enumeration: codes eq map
-- statement:
--   The Weighted Near Enumeration construction uses the codes eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L134-L146
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearEnumeration.lean#L134-L146

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_NearEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_eq_map
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_eq_map

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedEnumeration

theorem ThreeSum.WeightedNearEnumeration.codes_eq_map (qs : List ℕ) (D : ℕ) : codes qs D = (words qs D).map code := by sorry
