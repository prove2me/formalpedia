-- Prove2me | Theorems.Thm_Sendov_R_le_of_integral_le
-- name    : Sendov.R_le_of_integral_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:10.068674+00:00
-- url     : https://prove2.me/theorems/031a6683-c85b-5f63-8885-9de2ddb54dd0
-- title:
--   Sendov: R le of integral le
-- statement:
--   The coefficient multiplying the integral in `Sendov.R` is nonnegative, so any upper
--   bound for the integral yields an upper bound for `R`.  This is how each degree replaces its
--   integral by an explicit rational function.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Basic.lean#L116-L129
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Basic.lean#L116-L129

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}

theorem Sendov.R_le_of_integral_le (hn : 2 ≤ n) (hα : 0 ≤ α) {J : ℝ}
    (hJ : (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)) ≤ J) :
    R n α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α)) +
      A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) * J := by sorry
