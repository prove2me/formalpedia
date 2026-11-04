-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedDigits_evaluate_digits_of_lt
-- name    : ThreeSum.TernarySignedDigits.evaluate_digits_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:24:23.675206+00:00
-- url     : https://prove2.me/theorems/b375f1c1-2e5c-491f-bfab-201c135deeb2
-- title:
--   Ternary Signed Digits: evaluate digits of lt
-- statement:
--   The Ternary Signed Digits construction uses the evaluate digits of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L66-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L66-L69

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

theorem ThreeSum.TernarySignedDigits.evaluate_digits_of_lt {b x J : ℕ} (h : x < b^J) :
    evaluate b J (fun j => (digit b x j : ℤ))=(x : ℤ) := by sorry
