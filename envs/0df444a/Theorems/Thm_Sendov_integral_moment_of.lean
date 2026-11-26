-- Prove2me | Theorems.Thm_Sendov_integral_moment_of
-- name    : Sendov.integral_moment_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:48.168668+00:00
-- url     : https://prove2.me/theorems/af7aa41e-b206-5f16-b76b-ddfee718b808
-- title:
--   Sendov: integral moment of
-- statement:
--   **The moment for a given degree, by the recurrence.**  Every ingredient on the right is
--   a kernel computation on integers, apart from the final evaluation at `α`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L255-L260
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Recurrence.lean#L255-L260

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.integral_moment_of (n k : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ k)
      = irow (qrow (gg0 n) (gg1 n) (gg2 n) k) 0 α / (2 * M n * (3 + α)) ^ k := by sorry
