-- Prove2me | Theorems.Thm_Sendov_R_twenty_le
-- name    : Sendov.R_twenty_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:01:05.164322+00:00
-- url     : https://prove2.me/theorems/ffa5a2e2-8afa-568b-b22c-1f84dd3fd2a4
-- title:
--   Sendov: R twenty le
-- statement:
--   The upper bound for `R 20 α`, from the general moment formula with `k = 8`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20.lean#L114-L124
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20.lean#L114-L124

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20
set_option autoImplicit false
set_option maxRecDepth 8000
open Sendov
open MeasureTheory
variable {α : ℝ}

theorem Sendov.R_twenty_le (hα : 0 ≤ α) :
    R 20 α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / 38 + 1 / (76 * (3 + α))
      + 1710 * A 20 α ^ 2 / (3 + α) * mom 20 α 8 := by sorry
