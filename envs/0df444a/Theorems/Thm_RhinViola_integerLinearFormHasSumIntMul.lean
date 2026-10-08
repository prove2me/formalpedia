-- Prove2me | Theorems.Thm_RhinViola_integerLinearFormHasSumIntMul
-- name    : RhinViola.integerLinearFormHasSumIntMul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T00:04:22.125996+00:00
-- url     : https://prove2.me/theorems/c516ef46-5a93-4922-992b-2b6dcc729e49
-- title:
--   Integer-linear-form HasSum statements are closed under integer scaling
-- statement:
--   Multiplying every term of a convergent series by an integer preserves the lattice Z + Z alpha: the two integer coefficients are multiplied by the same integer.
-- source:
--   Elementary closure property used in the arithmetic assembly of the Rhin-Viola linear forms.

import Mathlib.Tactic

theorem RhinViola.integerLinearFormHasSumIntMul
    (α : ℝ) (f : ℕ → ℝ) (r z c : ℤ)
    (hf : HasSum f ((z : ℝ) + (c : ℝ) * α)) :
    HasSum (fun k : ℕ => (r : ℝ) * f k)
      (((r * z : ℤ) : ℝ) + (((r * c : ℤ) : ℝ) * α)) := by sorry
