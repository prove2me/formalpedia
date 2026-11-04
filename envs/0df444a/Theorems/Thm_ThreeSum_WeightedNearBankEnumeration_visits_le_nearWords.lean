-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_visits_le_nearWords
-- name    : ThreeSum.WeightedNearBankEnumeration.visits_le_nearWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:43.85091+00:00
-- url     : https://prove2.me/theorems/5912bb3b-856b-4a77-979a-f4ff46770778
-- title:
--   Weighted Near Bank Enumeration: visits le near Words
-- statement:
--   The Weighted Near Bank Enumeration construction uses the visits le near Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean#L82-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean#L82-L85

import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_BankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_Weighted_NearBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration
open WeightedCache (Below)
open ThreeSum.WeightedEnumeration (digitCost)

theorem ThreeSum.WeightedNearBankEnumeration.visits_le_nearWords {N : ℕ} (Q : TritWord N) (D : ℕ) :
    WeightedNearEnumeration.visits (wordList Q) D ≤ (N+1)*(nearWords Q D).card := by sorry
