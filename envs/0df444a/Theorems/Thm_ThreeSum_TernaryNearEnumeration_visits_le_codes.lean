-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearEnumeration_visits_le_codes
-- name    : ThreeSum.TernaryNearEnumeration.visits_le_codes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:24.46055+00:00
-- url     : https://prove2.me/theorems/4e64af15-b3f2-4c29-bca7-88d4c4960658
-- title:
--   Ternary Near Enumeration: visits le codes
-- statement:
--   The Ternary Near Enumeration construction uses the visits le codes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L215-L217
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L215-L217

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_visits_le_codes

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses

theorem ThreeSum.TernaryNearEnumeration.visits_le_codes (qs : List ℕ) (D : ℕ) :
    visits qs D ≤ (qs.length+1)*(codes qs D).length := by sorry
