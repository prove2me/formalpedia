-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankEnumeration_words_image_bank
-- name    : ThreeSum.TernaryBankEnumeration.words_image_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:36:03.100026+00:00
-- url     : https://prove2.me/theorems/382705f7-885e-440b-b7d1-d7bf3ff2e8cf
-- title:
--   Ternary Bank Enumeration: words image bank
-- statement:
--   The Ternary Bank Enumeration construction uses the words image bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L50-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L50-L65

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryBankEnumeration.words_image_bank (N T : ℕ) :
    (words N T).toFinset = (bank N T).image wordList := by sorry
