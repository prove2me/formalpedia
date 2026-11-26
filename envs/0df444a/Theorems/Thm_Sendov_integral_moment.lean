-- Prove2me | Theorems.Thm_Sendov_integral_moment
-- name    : Sendov.integral_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:55:59.588529+00:00
-- url     : https://prove2.me/theorems/cc2d563c-0dab-5bd2-b6a4-7ac138b7d135
-- title:
--   Sendov: integral moment
-- statement:
--   **The moment formula.**  The integrals appearing in `Sendov.R` are exactly the finite
--   double sum `Sendov.mom`, for every natural `k`, with no hypotheses at all.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Moments.lean#L88-L108
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Moments.lean#L88-L108

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Moments
set_option autoImplicit false
open Sendov
open MeasureTheory Finset

theorem Sendov.integral_moment (n : ℕ) (α : ℝ) (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ k) = mom n α k := by sorry
