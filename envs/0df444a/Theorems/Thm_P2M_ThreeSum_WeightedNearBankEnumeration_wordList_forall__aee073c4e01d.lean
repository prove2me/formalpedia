-- Prove2me | Theorems.Thm_P2M_ThreeSum_WeightedNearBankEnumeration_wordList_forall__aee073c4e01d
-- name    : P2M_ThreeSum_WeightedNearBankEnumeration_wordList_forall__aee073c4e01d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:47.714237+00:00
-- url     : https://prove2.me/theorems/9343fa0f-6b84-43d6-8a10-2e016deeb350
-- title:
--   P2 M Three Sum Weighted Near Bank Enumeration word List forall  aee073c4e01d: P2 M Three Sum Weighted Near Bank Enumeration word List forall  aee073c4e01d
-- statement:
--   The P2 M Three Sum Weighted Near Bank Enumeration word List forall  aee073c4e01d construction uses the P2 M Three Sum Weighted Near Bank Enumeration word List forall  aee073c4e01d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean#L24-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean#L24-L37

import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_BankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_Weighted_NearBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration
open WeightedCache (Below)
open ThreeSum.WeightedEnumeration (digitCost)

theorem P2M_ThreeSum_WeightedNearBankEnumeration_wordList_forall__aee073c4e01d {N : ℕ} (R Q : TritWord N) :
    List.Forall₂ (· ≤ ·) (wordList R) (wordList Q) ↔ Below R Q := by sorry

alias «ThreeSum».«WeightedNearBankEnumeration».«wordList_forall₂» := P2M_ThreeSum_WeightedNearBankEnumeration_wordList_forall__aee073c4e01d
