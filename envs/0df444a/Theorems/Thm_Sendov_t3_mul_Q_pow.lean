-- Prove2me | Theorems.Thm_Sendov_t3_mul_Q_pow
-- name    : Sendov.t3_mul_Q_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:54:11.579675+00:00
-- url     : https://prove2.me/theorems/b03f75ee-a18c-4c8e-b1cc-5d03e453f170
-- title:
--   Sendov: t3 mul Q pow
-- statement:
--   The expansion of the integrand of `Sendov.R` as an explicit polynomial.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Moments.lean#L61-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Moments.lean#L61-L77

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Moments
set_option autoImplicit false
open Sendov
open MeasureTheory Finset

theorem Sendov.t3_mul_Q_pow (n : ℕ) (α t : ℝ) (k : ℕ) :
    t ^ 3 * Q n α t ^ k
      = ∑ i ∈ range (k + 1), ∑ l ∈ range (i + 1),
          ((k.choose i : ℝ) * (i.choose l) * (-2 * c n α) ^ l * A n α ^ (i - l))
            * t ^ (2 * i - l + 3) := by sorry
