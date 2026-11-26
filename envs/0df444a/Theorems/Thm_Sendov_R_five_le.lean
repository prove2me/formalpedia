-- Prove2me | Theorems.Thm_Sendov_R_five_le
-- name    : Sendov.R_five_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:57:15.206893+00:00
-- url     : https://prove2.me/theorems/07d9051c-46eb-4126-9ac6-438f7e181fdf
-- title:
--   Sendov: R five le
-- statement:
--   The upper bound for `R 5 α` obtained from `Sendov.integral_five`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree5.lean#L83-L90
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree5.lean#L83-L90

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Degree5
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}

theorem Sendov.R_five_le (hα : 0 ≤ α) (hfeas : c 5 α ^ 2 ≤ A 5 α) :
    R 5 α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / 8 + 1 / (16 * (3 + α))
      + 60 * A 5 α ^ 2 / (4 * (3 + α))
        * (3 / 2 * (1 / 4 - 2 * c 5 α / 5 + A 5 α / 6) + 1 / 24) := by sorry
