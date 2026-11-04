-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
-- name    : ThreeSum.TernaryNearEnumeration.codes_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:17.240119+00:00
-- url     : https://prove2.me/theorems/3f0da7b2-5742-438a-82aa-b5dfa92f7859
-- title:
--   Ternary Near Enumeration: codes length
-- statement:
--   The Ternary Near Enumeration construction uses the codes length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L143-L144
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L143-L144

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
attribute [local simp] ThreeSum.TernaryAddresses.codes_length


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses

theorem ThreeSum.TernaryNearEnumeration.codes_length (qs : List ℕ) (D : ℕ) :
    (codes qs D).length = (words qs D).length := by sorry
