-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_injective
-- name    : ThreeSum.WeightedBankEnumeration.wordList_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:41.46379+00:00
-- url     : https://prove2.me/theorems/2f80cf77-d2f1-4a6b-99ea-0e5b261f533c
-- title:
--   Weighted Bank Enumeration: word List injective
-- statement:
--   The Weighted Bank Enumeration construction uses the word List injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L41-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L41-L46

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType

theorem ThreeSum.WeightedBankEnumeration.wordList_injective (N : ℕ) : Function.Injective (@wordList N) := by sorry
