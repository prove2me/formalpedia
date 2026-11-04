-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_wordList_deficit
-- name    : ThreeSum.WeightedNearBankEnumeration.wordList_deficit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:39.20888+00:00
-- url     : https://prove2.me/theorems/13cadcb2-62ca-4bec-9984-cbe1cdf628a4
-- title:
--   Weighted Near Bank Enumeration: word List deficit
-- statement:
--   The Weighted Near Bank Enumeration construction uses the word List deficit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean#L39-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean#L39-L48

import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_BankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_Weighted_NearBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration
open WeightedCache (Below)
open ThreeSum.WeightedEnumeration (digitCost)

theorem ThreeSum.WeightedNearBankEnumeration.wordList_deficit {N : ℕ} (Q R : TritWord N) :
    (List.zipWith (fun q r => digitCost q-digitCost r) (wordList Q) (wordList R)).sum = deficit Q R := by sorry
