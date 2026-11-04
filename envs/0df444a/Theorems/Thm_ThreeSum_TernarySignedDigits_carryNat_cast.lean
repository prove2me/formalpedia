-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedDigits_carryNat_cast
-- name    : ThreeSum.TernarySignedDigits.carryNat_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:24:23.507339+00:00
-- url     : https://prove2.me/theorems/48cb019b-3646-4c63-be60-7a5ead6ba152
-- title:
--   Ternary Signed Digits: carry Nat cast
-- statement:
--   The Ternary Signed Digits construction uses the carry Nat cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L33-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L33-L39

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

theorem ThreeSum.TernarySignedDigits.carryNat_cast (b x y j : ℕ) :
    (carryNat b x y j : ℤ)=(quotient b (x+y) j : ℤ)-(quotient b x j : ℤ)-(quotient b y j : ℤ) := by sorry
