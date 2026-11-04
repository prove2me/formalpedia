-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_mem_words
-- name    : ThreeSum.WeightedBankEnumeration.wordList_mem_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:41.168319+00:00
-- url     : https://prove2.me/theorems/5cdee0a4-6afd-4689-943b-c979559fd752
-- title:
--   Weighted Bank Enumeration: word List mem words
-- statement:
--   The Weighted Bank Enumeration construction uses the word List mem words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L48-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L48-L52

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType

theorem ThreeSum.WeightedBankEnumeration.wordList_mem_words {N T : ℕ} (w : TritWord N) :
    wordList w ∈ words N T ↔ w ∈ bank N T := by sorry
