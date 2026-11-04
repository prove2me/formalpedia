-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedDigits_quotient_step
-- name    : ThreeSum.TernarySignedDigits.quotient_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:37.12596+00:00
-- url     : https://prove2.me/theorems/965e34db-6bb5-4d81-9a76-d089c2149839
-- title:
--   Ternary Signed Digits: quotient step
-- statement:
--   The Ternary Signed Digits construction uses the quotient step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L17-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedDigits.lean#L17-L19

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

theorem ThreeSum.TernarySignedDigits.quotient_step (b x j : ℕ) : quotient b x j/b=quotient b x (j+1) := by sorry
