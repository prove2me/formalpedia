-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_digits
-- name    : ThreeSum.WeightedBankEnumeration.wordList_digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:40.271203+00:00
-- url     : https://prove2.me/theorems/6e447851-01f9-47a1-8c25-f723ef59cbb5
-- title:
--   Weighted Bank Enumeration: word List digits
-- statement:
--   The Weighted Bank Enumeration construction uses the word List digits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L36-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L36-L39

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType

theorem ThreeSum.WeightedBankEnumeration.wordList_digits {N : ℕ} (w : TritWord N) : ∀ d ∈ wordList w, d < 3 := by sorry
