-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedDigits_addition_iff_carry
-- name    : ThreeSum.TernarySignedDigits.addition_iff_carry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:24:33.239205+00:00
-- url     : https://prove2.me/theorems/c6002eef-903c-411c-963c-2f8988661315
-- title:
--   Ternary Signed Digits: addition iff carry
-- statement:
--   The Ternary Signed Digits construction uses the addition iff carry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L127-L132
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L127-L132

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

theorem ThreeSum.TernarySignedDigits.addition_iff_carry {b J x y z : ℕ} (hx : x<b^J) (hy : y<b^J) (hz : z<b^J) :
    x+y=z ↔ ∃ c : CarryWord J, ValidCarry c ∧ DigitRelation b J x y z c := by sorry
