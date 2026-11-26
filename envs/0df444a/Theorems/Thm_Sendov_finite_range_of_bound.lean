-- Prove2me | Theorems.Thm_Sendov_finite_range_of_bound
-- name    : Sendov.finite_range_of_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:12:35.385411+00:00
-- url     : https://prove2.me/theorems/bf7e833e-21c8-41b5-9550-ae12fcbfe6e6
-- title:
--   Sendov: finite range of bound
-- statement:
--   **The reduction.**  Any upper bound `J` for the integral turns `R n α < 1` into an
--   inequality between explicit rational functions of `α`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Reduce.lean#L69-L74
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Reduce.lean#L69-L74

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Reduce
set_option autoImplicit false
open Sendov
open MeasureTheory Finset
variable {n : ℕ} {α w : ℝ}

theorem Sendov.finite_range_of_bound (hn : 2 ≤ n) (hα : 0 ≤ α) {J : ℝ}
    (hJ : (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)) ≤ J)
    (h : 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α))
      + A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) * J < 1) :
    R n α < 1 := by sorry
