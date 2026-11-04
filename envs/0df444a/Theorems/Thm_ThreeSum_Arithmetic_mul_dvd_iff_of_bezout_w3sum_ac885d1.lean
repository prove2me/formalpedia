-- Prove2me | Theorems.Thm_ThreeSum_Arithmetic_mul_dvd_iff_of_bezout_w3sum_ac885d1
-- name    : ThreeSum.Arithmetic.mul_dvd_iff_of_bezout_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:47.473116+00:00
-- url     : https://prove2.me/theorems/eace01ef-d2e0-40dc-833a-3092bd7333ed
-- title:
--   Arithmetic: mul dvd iff of bezout
-- statement:
--   A concrete Bezout witness is enough for the product-divisibility
--   identity.  The statement does not assume primality or that the arithmetic
--   modulus is prime.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L146-L165
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Arithmetic.lean#L146-L165

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

theorem ThreeSum.Arithmetic.mul_dvd_iff_of_bezout_w3sum_ac885d1 {m l x : ℤ}
    (hbez : ∃ u v : ℤ, u * m + v * l = 1) :
    m * l ∣ x ↔ m ∣ x ∧ l ∣ x := by sorry
