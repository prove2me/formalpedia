-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalBank_bank_card_le
-- name    : ThreeSum.WeightedGlobalBank.bank_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:19:37.149692+00:00
-- url     : https://prove2.me/theorems/812db118-3350-460b-a502-5e5fb19913d2
-- title:
--   Weighted Global Bank: bank card le
-- statement:
--   The Weighted Global Bank construction uses the bank card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalBank.lean#L21-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalBank.lean#L21-L22

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_GlobalBank
import Theorems.Thm_ThreeSum_TernaryBank_bank_card_le

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalBank
open TernaryJointType

theorem ThreeSum.WeightedGlobalBank.bank_card_le (N T : ℕ) : (bank N T).card≤3^N := by sorry
