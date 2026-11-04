-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_words_image_nearWords
-- name    : ThreeSum.WeightedNearBankEnumeration.words_image_nearWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:46.923751+00:00
-- url     : https://prove2.me/theorems/a0d5dc98-b614-4a73-8c12-884b33f8f510
-- title:
--   Weighted Near Bank Enumeration: words image near Words
-- statement:
--   The Weighted Near Bank Enumeration construction uses the words image near Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean#L55-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean#L55-L73

import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_BankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_Weighted_NearBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration
open WeightedCache (Below)
open ThreeSum.WeightedEnumeration (digitCost)

theorem ThreeSum.WeightedNearBankEnumeration.words_image_nearWords {N : ℕ} (Q : TritWord N) (D : ℕ) :
    (WeightedNearEnumeration.words (wordList Q) D).toFinset =
      (nearWords Q D).image wordList := by sorry
