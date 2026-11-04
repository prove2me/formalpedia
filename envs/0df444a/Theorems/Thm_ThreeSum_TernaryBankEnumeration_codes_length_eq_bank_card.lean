-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankEnumeration_codes_length_eq_bank_card
-- name    : ThreeSum.TernaryBankEnumeration.codes_length_eq_bank_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:36:01.819991+00:00
-- url     : https://prove2.me/theorems/d7d1a27d-6525-48f1-8e79-fc80b019879e
-- title:
--   Ternary Bank Enumeration: codes length eq bank card
-- statement:
--   The Ternary Bank Enumeration construction uses the codes length eq bank card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L72-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L72-L75

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryBankEnumeration.codes_length_eq_bank_card (N T : ℕ) :
    (codes N T).length = (bank N T).card := by sorry
