-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalBank_bank_card_gibbs
-- name    : ThreeSum.WeightedGlobalBank.bank_card_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:16:28.832166+00:00
-- url     : https://prove2.me/theorems/b2203618-be05-4df7-998f-e10e7d169753
-- title:
--   Weighted Global Bank: bank card gibbs
-- statement:
--   The Weighted Global Bank construction uses the bank card gibbs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalBank.lean#L28-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalBank.lean#L28-L31

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_GlobalBank
import Theorems.Thm_ThreeSum_TernaryBank_bank_card_gibbs
import Theorems.Thm_WeightedCache_bank_card_gibbs

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalBank
open TernaryJointType

theorem ThreeSum.WeightedGlobalBank.bank_card_gibbs (N T : ℕ) (y : ℝ) (hy : 0≤y) (hy1 : y≤1) :
    (bank N T).card*y^T≤(1+y^512+y^1025)^N := by sorry
