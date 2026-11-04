-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_guarded_lift_unique
-- name    : ThreeSum.Arithmetic.guarded_lift_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:43.710347+00:00
-- url     : https://prove2.me/theorems/0560055e-3ee9-42f6-b85b-4bed3f8f8b99
-- title:
--   Arithmetic: guarded lift unique
-- statement:
--   Distinct signed lifts of a fixed A residue never give the same radix
--   query key under the range guard.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L75-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L75-L88

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

theorem ThreeSum.Arithmetic.guarded_lift_unique {P R a d j k : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ R)
    (hj : SmallLift j) (hk : SmallLift k)
    (hcong : R ∣ (a + j * P + d) - (a + k * P + d)) : j = k := by sorry
