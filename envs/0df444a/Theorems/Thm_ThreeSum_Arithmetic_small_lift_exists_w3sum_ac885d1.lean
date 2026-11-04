-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_small_lift_exists_w3sum_ac885d1
-- name    : ThreeSum.Arithmetic.small_lift_exists_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:45.392093+00:00
-- url     : https://prove2.me/theorems/857b7da3-105c-410b-9432-da45eb2b2176
-- title:
--   Arithmetic: small lift exists
-- statement:
--   Completeness of the signed-lift list for any modular candidate.
--   In fact, canonical residues only need the lifts -1 and 0.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L119-L139
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L119-L139

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Arithmetic
set_option autoImplicit false
open ThreeSum ThreeSum.Arithmetic
open Finset
open scoped BigOperators

theorem ThreeSum.Arithmetic.small_lift_exists_w3sum_ac885d1 {P a b c : ℤ} (hP : 0 < P)
    (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P)
    (hc0 : 0 ≤ c) (hcP : c < P)
    (hdiv : P ∣ c - b - a) :
    ∃ j : ℤ, SmallLift j ∧ c - b = a + j * P := by sorry
