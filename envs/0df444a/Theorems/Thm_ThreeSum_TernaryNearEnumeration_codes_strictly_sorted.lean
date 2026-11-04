-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_strictly_sorted
-- name    : ThreeSum.TernaryNearEnumeration.codes_strictly_sorted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:25.15486+00:00
-- url     : https://prove2.me/theorems/4df11a68-de12-4c9e-a90c-edde415e74ac
-- title:
--   Ternary Near Enumeration: codes strictly sorted
-- statement:
--   The Ternary Near Enumeration construction uses the codes strictly sorted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L153-L175
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L153-L175

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_strictly_sorted

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses

theorem ThreeSum.TernaryNearEnumeration.codes_strictly_sorted (qs : List ℕ) (D : ℕ) (hq : ∀ q ∈ qs, q < 3) :
    (codes qs D).Pairwise (· < ·) := by sorry
