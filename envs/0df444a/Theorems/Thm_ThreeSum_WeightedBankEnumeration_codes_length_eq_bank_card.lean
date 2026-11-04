-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankEnumeration_codes_length_eq_bank_card
-- name    : ThreeSum.WeightedBankEnumeration.codes_length_eq_bank_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:44.372299+00:00
-- url     : https://prove2.me/theorems/223ef30c-7146-4600-8937-c35f7129aeec
-- title:
--   Weighted Bank Enumeration: codes length eq bank card
-- statement:
--   The Weighted Bank Enumeration construction uses the codes length eq bank card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L87-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L87-L90

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType

theorem ThreeSum.WeightedBankEnumeration.codes_length_eq_bank_card (N T : ℕ) :
    (codes N T).length = (bank N T).card := by sorry
