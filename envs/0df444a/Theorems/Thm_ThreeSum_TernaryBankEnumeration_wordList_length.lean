-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
-- name    : ThreeSum.TernaryBankEnumeration.wordList_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:55.294885+00:00
-- url     : https://prove2.me/theorems/a5070bc7-9e60-43eb-9cb9-076769a3d341
-- title:
--   Ternary Bank Enumeration: word List length
-- statement:
--   The Ternary Bank Enumeration construction uses the word List length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L15-L16
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L15-L16

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryBankEnumeration.wordList_length {N : ℕ} (w : TritWord N) : (wordList w).length = N := by sorry
