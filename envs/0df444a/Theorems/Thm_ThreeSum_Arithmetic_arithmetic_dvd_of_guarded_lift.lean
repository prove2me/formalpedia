-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_arithmetic_dvd_of_guarded_lift
-- name    : ThreeSum.Arithmetic.arithmetic_dvd_of_guarded_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:41.573005+00:00
-- url     : https://prove2.me/theorems/b8b6ff8f-2243-4d63-adca-b4034a1cff09
-- title:
--   Arithmetic: arithmetic dvd of guarded lift
-- statement:
--   A queried representation cannot introduce an alias that fails the
--   arithmetic congruence.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L61-L71
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L61-L71

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

theorem ThreeSum.Arithmetic.arithmetic_dvd_of_guarded_lift {P R a b c d j : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R)
    (ha0 : 0 ≤ a) (haP : a < P)
    (hb0 : 0 ≤ b) (hbP : b < P)
    (hc0 : 0 ≤ c) (hcP : c < P)
    (hj : SmallLift j)
    (hcong : R ∣ (c + d - b) - (a + j * P + d)) :
    P ∣ c - b - a := by sorry
