-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
-- name    : ThreeSum.WeightedBankEnumeration.wordList_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:35.960192+00:00
-- url     : https://prove2.me/theorems/b6c9e8f2-ce5d-4637-a245-511601a6c7b4
-- title:
--   Weighted Bank Enumeration: word List cost
-- statement:
--   The Weighted Bank Enumeration construction uses the word List cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L32-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L32-L34

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType

theorem ThreeSum.WeightedBankEnumeration.wordList_cost {N : ℕ} (w : TritWord N) :
    ((wordList w).map digitCost).sum = cacheCost w := by sorry
