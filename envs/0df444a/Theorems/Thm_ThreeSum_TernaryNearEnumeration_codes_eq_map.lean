-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_eq_map
-- name    : ThreeSum.TernaryNearEnumeration.codes_eq_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:15.559567+00:00
-- url     : https://prove2.me/theorems/19367fcd-c10e-44c4-866e-b4eb7dbb1079
-- title:
--   Ternary Near Enumeration: codes eq map
-- statement:
--   The Ternary Near Enumeration construction uses the codes eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L129-L141
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L129-L141

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_eq_map

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses

theorem ThreeSum.TernaryNearEnumeration.codes_eq_map (qs : List ℕ) (D : ℕ) : codes qs D = (words qs D).map code := by sorry
