-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_eq_zero_of_dvd_of_bounds
-- name    : ThreeSum.Arithmetic.eq_zero_of_dvd_of_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:39.335905+00:00
-- url     : https://prove2.me/theorems/db8c537f-d0ce-4a4d-bb37-23ff50f73817
-- title:
--   Arithmetic: eq zero of dvd of bounds
-- statement:
--   A multiple of a positive modulus strictly between its two nearest
--   nonzero multiples must vanish.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L26-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L26-L36

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

theorem ThreeSum.Arithmetic.eq_zero_of_dvd_of_bounds {R x : ℤ} (hR : 0 < R)
    (hlo : -R < x) (hhi : x < R) (hdiv : R ∣ x) : x = 0 := by sorry
