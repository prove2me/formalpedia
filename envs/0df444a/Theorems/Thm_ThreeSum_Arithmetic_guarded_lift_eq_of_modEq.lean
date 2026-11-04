-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_guarded_lift_eq_of_modEq
-- name    : ThreeSum.Arithmetic.guarded_lift_eq_of_modEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:45.179444+00:00
-- url     : https://prove2.me/theorems/f4b5581c-b0ca-4c43-8e60-3bd40d99be06
-- title:
--   Arithmetic: guarded lift eq of mod Eq
-- statement:
--   The actual modulo-key interface, before lifting back to original values.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L91-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L91-L99

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

theorem ThreeSum.Arithmetic.guarded_lift_eq_of_modEq {P R a b c d j : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R)
    (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P)
    (hc0 : 0 ≤ c) (hcP : c < P)
    (hj : SmallLift j)
    (hkey : Int.ModEq R (a + j * P + d) (c + d - b)) :
    c - b = a + j * P := by sorry
