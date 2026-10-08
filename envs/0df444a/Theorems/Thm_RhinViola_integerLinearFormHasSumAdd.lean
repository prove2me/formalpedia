-- Prove2me | Theorems.Thm_RhinViola_integerLinearFormHasSumAdd
-- name    : RhinViola.integerLinearFormHasSumAdd
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T00:04:15.715373+00:00
-- url     : https://prove2.me/theorems/607210fc-832d-4f94-96b0-8a7798c91e15
-- title:
--   Integer-linear-form HasSum statements are closed under addition
-- statement:
--   If two convergent series have sums in the integer lattice Z + Z alpha, then their termwise sum also has a sum in Z + Z alpha, with the two integer coefficients added.
-- source:
--   Elementary closure property used in the arithmetic assembly of the Rhin-Viola linear forms.

import Mathlib.Tactic

theorem RhinViola.integerLinearFormHasSumAdd
    (α : ℝ) (f g : ℕ → ℝ) (z₁ z₂ c₁ c₂ : ℤ)
    (hf : HasSum f ((z₁ : ℝ) + (c₁ : ℝ) * α))
    (hg : HasSum g ((z₂ : ℝ) + (c₂ : ℝ) * α)) :
    HasSum (fun k : ℕ => f k + g k)
      (((z₁ + z₂ : ℤ) : ℝ) + (((c₁ + c₂ : ℤ) : ℝ) * α)) := by sorry
