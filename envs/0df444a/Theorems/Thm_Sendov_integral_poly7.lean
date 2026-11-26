-- Prove2me | Theorems.Thm_Sendov_integral_poly7
-- name    : Sendov.integral_poly7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:34.194333+00:00
-- url     : https://prove2.me/theorems/aaec4f02-e7ed-5d15-8a9a-a9a495931293
-- title:
--   Sendov: integral poly7
-- statement:
--   The moments of a polynomial supported in degrees three to seven, kept as a convenience
--   for the low degrees.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Moments.lean#L112-L129
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Moments.lean#L112-L129

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Moments
set_option autoImplicit false
open Sendov
open MeasureTheory Finset

theorem Sendov.integral_poly7 (a₀ a₁ a₂ a₃ a₄ : ℝ) :
    (∫ t in (0 : ℝ)..1, (a₀ * t ^ 3 + a₁ * t ^ 4 + a₂ * t ^ 5 + a₃ * t ^ 6 + a₄ * t ^ 7))
      = a₀ / 4 + a₁ / 5 + a₂ / 6 + a₃ / 7 + a₄ / 8 := by sorry
