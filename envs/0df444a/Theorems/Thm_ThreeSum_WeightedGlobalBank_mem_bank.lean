-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_bank
-- name    : ThreeSum.WeightedGlobalBank.mem_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:15:25.129138+00:00
-- url     : https://prove2.me/theorems/906fb8e7-5f48-4a8d-93b3-3477144257ff
-- title:
--   Weighted Global Bank: mem bank
-- statement:
--   The Weighted Global Bank construction uses the mem bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalBank.lean#L17-L18
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalBank.lean#L17-L18

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_GlobalBank
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalBank
open TernaryJointType

theorem ThreeSum.WeightedGlobalBank.mem_bank {N T : ℕ} {R : TritWord N} : R∈bank N T ↔ cacheCost R≤T := by sorry
