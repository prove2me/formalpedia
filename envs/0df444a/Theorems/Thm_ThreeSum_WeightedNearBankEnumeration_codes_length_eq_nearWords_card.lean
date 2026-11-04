-- Prove2me | Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_codes_length_eq_nearWords_card
-- name    : ThreeSum.WeightedNearBankEnumeration.codes_length_eq_nearWords_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:54.960372+00:00
-- url     : https://prove2.me/theorems/91883543-c99a-4763-b982-7164f372722b
-- title:
--   Weighted Near Bank Enumeration: codes length eq near Words card
-- statement:
--   The Weighted Near Bank Enumeration construction uses the codes length eq near Words card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean#L75-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearBankEnumeration.lean#L75-L80

import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_BankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_Weighted_NearBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration
open WeightedCache (Below)
open ThreeSum.WeightedEnumeration (digitCost)

theorem ThreeSum.WeightedNearBankEnumeration.codes_length_eq_nearWords_card {N : ℕ} (Q : TritWord N) (D : ℕ) :
    (WeightedNearEnumeration.codes (wordList Q) D).length = (nearWords Q D).card := by sorry
