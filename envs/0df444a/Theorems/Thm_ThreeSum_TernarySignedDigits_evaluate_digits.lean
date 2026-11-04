-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedDigits_evaluate_digits
-- name    : ThreeSum.TernarySignedDigits.evaluate_digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:24:22.014861+00:00
-- url     : https://prove2.me/theorems/4512a8d2-a3b4-4a00-aa49-d5688de71df7
-- title:
--   Ternary Signed Digits: evaluate digits
-- statement:
--   The Ternary Signed Digits construction uses the evaluate digits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L57-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L57-L64

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

theorem ThreeSum.TernarySignedDigits.evaluate_digits (b x J : ℕ) :
    evaluate b J (fun j => (digit b x j : ℤ))=(x : ℤ)-(b : ℤ)^J*(quotient b x J : ℤ) := by sorry
