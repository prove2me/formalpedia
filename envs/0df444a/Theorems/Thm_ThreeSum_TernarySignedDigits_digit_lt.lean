-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedDigits_digit_lt
-- name    : ThreeSum.TernarySignedDigits.digit_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:35.276884+00:00
-- url     : https://prove2.me/theorems/47ee8aed-5bff-42eb-a8b1-3bf2fc2b20d8
-- title:
--   Ternary Signed Digits: digit lt
-- statement:
--   The Ternary Signed Digits construction uses the digit lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L16-L16
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L16-L16

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

theorem ThreeSum.TernarySignedDigits.digit_lt {b : ℕ} (hb : 0 < b) (x j : ℕ) : digit b x j < b := by sorry
