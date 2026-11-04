-- Prove2me | Theorems.Thm_ThreeSum_TernaryCarryCode_digit_ofDigits
-- name    : ThreeSum.TernaryCarryCode.digit_ofDigits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:06:58.190599+00:00
-- url     : https://prove2.me/theorems/79265ed0-9e2c-418f-a178-2aed5714e56c
-- title:
--   Ternary Carry Code: digit of Digits
-- statement:
--   The Ternary Carry Code construction uses the digit of Digits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCarryCode.lean#L23-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCarryCode.lean#L23-L35

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernaryCarryCode.digit_ofDigits {b : ℕ} (hb : 1<b) (l : List ℕ)
    (hl : ∀ x∈l, x<b) (j : ℕ) :
    digit b (Nat.ofDigits b l) j=l.getD j 0 := by sorry
