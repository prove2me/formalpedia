-- Prove2me | Theorems.Thm_Sendov_R_eight_le
-- name    : Sendov.R_eight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:54.959036+00:00
-- url     : https://prove2.me/theorems/9552e86e-d699-47b8-aff5-4b9b45eeae4a
-- title:
--   Sendov: R eight le
-- statement:
--   The upper bound for `R 8 α`, obtained from the general moment formula.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree8.lean#L51-L61
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree8.lean#L51-L61

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree8
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}

theorem Sendov.R_eight_le (hα : 0 ≤ α) :
    R 8 α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / 14 + 1 / (28 * (3 + α))
      + 84 * A 8 α ^ 2 / (3 + α) * mom 8 α 2 := by sorry
