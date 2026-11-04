-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_nearWords
-- name    : ThreeSum.WeightedGlobalBank.mem_nearWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:16:30.882041+00:00
-- url     : https://prove2.me/theorems/3a15a680-f5b8-4f75-9bd3-d160c64ea72f
-- title:
--   Weighted Global Bank: mem near Words
-- statement:
--   The Weighted Global Bank construction uses the mem near Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalBank.lean#L19-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalBank.lean#L19-L20

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_GlobalBank
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalBank
open TernaryJointType

theorem ThreeSum.WeightedGlobalBank.mem_nearWords {N D : ℕ} {R Q : TritWord N} :
    R∈nearWords Q D ↔ Below R Q ∧ deficit Q R≤D := by sorry
