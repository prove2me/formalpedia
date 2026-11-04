-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedDigits_carryAt_canonical
-- name    : ThreeSum.TernarySignedDigits.carryAt_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:24:26.485612+00:00
-- url     : https://prove2.me/theorems/b1bef3f6-7e96-481e-baa4-c277df10ca45
-- title:
--   Ternary Signed Digits: carry At canonical
-- statement:
--   The Ternary Signed Digits construction uses the carry At canonical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L89-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L89-L91

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

theorem ThreeSum.TernarySignedDigits.carryAt_canonical {b x y J j : ℕ} (hj : j ≤ J) :
    carryAt (canonicalCarry b x y J) j=(carryNat b x y j : ℤ) := by sorry
