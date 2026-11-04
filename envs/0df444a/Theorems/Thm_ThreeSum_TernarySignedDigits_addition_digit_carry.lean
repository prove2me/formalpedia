-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedDigits_addition_digit_carry
-- name    : ThreeSum.TernarySignedDigits.addition_digit_carry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:24:23.481028+00:00
-- url     : https://prove2.me/theorems/c9de48d1-dad5-45ec-8f63-90417802578a
-- title:
--   Ternary Signed Digits: addition digit carry
-- statement:
--   The Ternary Signed Digits construction uses the addition digit carry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L41-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L41-L45

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

theorem ThreeSum.TernarySignedDigits.addition_digit_carry (b x y j : ℕ) :
    (digit b x j : ℤ)+(digit b y j : ℤ)+(carryNat b x y j : ℤ)=
      (digit b (x+y) j : ℤ)+(b : ℤ)*(carryNat b x y (j+1) : ℤ) := by sorry
