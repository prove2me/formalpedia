-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_mem_words
-- name    : ThreeSum.TernaryBankEnumeration.wordList_mem_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:36:04.845206+00:00
-- url     : https://prove2.me/theorems/cef421ab-e01b-4c65-ba1c-8c2c3786143a
-- title:
--   Ternary Bank Enumeration: word List mem words
-- statement:
--   The Ternary Bank Enumeration construction uses the word List mem words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L33-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L33-L37

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryBankEnumeration.wordList_mem_words {N T : ℕ} (w : TritWord N) :
    wordList w ∈ words N T ↔ w ∈ bank N T := by sorry
