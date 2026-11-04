-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_guarded_remainder_lift_sound
-- name    : ThreeSum.Arithmetic.guarded_remainder_lift_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:48.437842+00:00
-- url     : https://prove2.me/theorems/daf39f35-e1db-4596-b0da-f69e825e7e19
-- title:
--   Arithmetic: guarded remainder lift sound
-- statement:
--   Guarded radix-key equality implies the arithmetic divisibility test on
--   the original signed integer values, not only on their canonical residues.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L103-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L103-L115

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

theorem ThreeSum.Arithmetic.guarded_remainder_lift_sound {P R a b c d j : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R) (hj : SmallLift j)
    (hkey : Int.ModEq R (a % P + j * P + d) (c % P + d - b % P)) :
    P ∣ c - b - a := by sorry
