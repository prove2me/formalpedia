-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
-- name    : ThreeSum.WeightedNearBankEnumeration.mem_nearWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:04:14.645952+00:00
-- url     : https://prove2.me/theorems/65b6b2a5-8aee-416e-b3ea-e290c1991003
-- title:
--   Weighted Near Bank Enumeration: mem near Words
-- statement:
--   The Weighted Near Bank Enumeration construction uses the mem near Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean#L20-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean#L20-L21

import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_BankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration
open WeightedCache (Below)
open ThreeSum.WeightedEnumeration (digitCost)

theorem ThreeSum.WeightedNearBankEnumeration.mem_nearWords {N D : ℕ} {Q R : TritWord N} :
    R∈nearWords Q D ↔ Below R Q ∧ deficit Q R≤D := by sorry
