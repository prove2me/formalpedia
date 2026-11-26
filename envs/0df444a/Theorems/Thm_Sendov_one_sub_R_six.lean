-- Prove2me | Theorems.Thm_Sendov_one_sub_R_six
-- name    : Sendov.one_sub_R_six
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:59:23.165357+00:00
-- url     : https://prove2.me/theorems/9fb0e27a-4df0-52d5-af4d-34359b3e4bbf
-- title:
--   Sendov: one sub R six
-- statement:
--   The cleared form of `1 - R 6 α`: the numerator is the quartic `P` and the denominator is
--   manifestly positive.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6.lean#L62-L69
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6.lean#L62-L69

import Definitions.Def_Sendov_Common_Basic
import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_Degree6
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}

theorem Sendov.one_sub_R_six (hα : 0 ≤ α) :
    1 - R 6 α
      = (-24 * α ^ 4 - 342 * α ^ 3 + 2345 * α ^ 2 - 900 * α + 1575) / (375 * (3 + α) ^ 2) := by sorry
