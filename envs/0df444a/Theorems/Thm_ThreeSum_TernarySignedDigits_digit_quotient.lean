-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedDigits_digit_quotient
-- name    : ThreeSum.TernarySignedDigits.digit_quotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:37.226531+00:00
-- url     : https://prove2.me/theorems/428b75b8-30fa-4a87-8957-a4795f5e7b57
-- title:
--   Ternary Signed Digits: digit quotient
-- statement:
--   The Ternary Signed Digits construction uses the digit quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L21-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L21-L26

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedDigits
open Finset
open scoped BigOperators

theorem ThreeSum.TernarySignedDigits.digit_quotient (b x j : ℕ) :
    (digit b x j : ℤ)=(quotient b x j : ℤ)-(b : ℤ)*(quotient b x (j+1) : ℤ) := by sorry
