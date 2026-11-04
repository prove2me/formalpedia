-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankEnumeration_words_image_bank
-- name    : ThreeSum.WeightedBankEnumeration.words_image_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:45.412044+00:00
-- url     : https://prove2.me/theorems/ea456102-9535-41c0-90c2-bc22fc0a5ab6
-- title:
--   Weighted Bank Enumeration: words image bank
-- statement:
--   The Weighted Bank Enumeration construction uses the words image bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L65-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L65-L80

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType

theorem ThreeSum.WeightedBankEnumeration.words_image_bank (N T : ℕ) :
    (words N T).toFinset = (bank N T).image wordList := by sorry
