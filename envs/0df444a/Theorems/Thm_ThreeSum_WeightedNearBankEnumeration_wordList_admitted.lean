-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_wordList_admitted
-- name    : ThreeSum.WeightedNearBankEnumeration.wordList_admitted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:40.235943+00:00
-- url     : https://prove2.me/theorems/740cf7bf-acc7-4739-8aa4-abbc1d8e0f58
-- title:
--   Weighted Near Bank Enumeration: word List admitted
-- statement:
--   The Weighted Near Bank Enumeration construction uses the word List admitted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean#L50-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean#L50-L53

import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_BankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_Weighted_NearBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration
open WeightedCache (Below)
open ThreeSum.WeightedEnumeration (digitCost)

theorem ThreeSum.WeightedNearBankEnumeration.wordList_admitted {N D : ℕ} (Q R : TritWord N) :
    WeightedNearEnumeration.Admitted (wordList Q) (wordList R) D ↔
      R ∈ nearWords Q D := by sorry
