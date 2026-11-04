-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankEnumeration_words_nodup
-- name    : ThreeSum.WeightedBankEnumeration.words_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:39.603677+00:00
-- url     : https://prove2.me/theorems/b26a3128-13ee-4092-8a25-d2501106185e
-- title:
--   Weighted Bank Enumeration: words nodup
-- statement:
--   The Weighted Bank Enumeration construction uses the words nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L82-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L82-L85

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType

theorem ThreeSum.WeightedBankEnumeration.words_nodup (N T : ℕ) : (words N T).Nodup := by sorry
