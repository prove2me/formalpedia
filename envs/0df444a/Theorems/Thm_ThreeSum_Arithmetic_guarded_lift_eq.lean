-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_guarded_lift_eq
-- name    : ThreeSum.Arithmetic.guarded_lift_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:42.318379+00:00
-- url     : https://prove2.me/theorems/4a333e2d-33a9-490b-a32f-c821f06ae7e9
-- title:
--   Arithmetic: guarded lift eq
-- statement:
--   With the range guard, a radix congruence for a normalized input triple
--   is an integer equality with one of the three arithmetic lifts.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L43-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L43-L57

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

theorem ThreeSum.Arithmetic.guarded_lift_eq {P R a b c d j : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R)
    (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P)
    (hc0 : 0 ≤ c) (hcP : c < P)
    (hj : SmallLift j)
    (hcong : R ∣ (c + d - b) - (a + j * P + d)) :
    c - b = a + j * P := by sorry
