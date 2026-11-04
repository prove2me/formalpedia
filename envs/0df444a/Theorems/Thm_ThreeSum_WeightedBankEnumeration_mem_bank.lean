-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
-- name    : ThreeSum.WeightedBankEnumeration.mem_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:29.947679+00:00
-- url     : https://prove2.me/theorems/b6113e9c-f4d5-42f6-995b-9609794f1f11
-- title:
--   Weighted Bank Enumeration: mem bank
-- statement:
--   The Weighted Bank Enumeration construction uses the mem bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L21-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L21-L22

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_bank


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType

theorem ThreeSum.WeightedBankEnumeration.mem_bank {N T : ℕ} {R : TritWord N} : R ∈ bank N T ↔ cacheCost R≤T := by sorry
