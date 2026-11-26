-- Prove2me | Theorems.Thm_Sendov_integral_six
-- name    : Sendov.integral_six
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:22.304058+00:00
-- url     : https://prove2.me/theorems/437c6d3d-77af-5c9a-b332-a5a8319eaeb1
-- title:
--   Sendov: integral six
-- statement:
--   In degree six the exponent `(n - 4) / 2` is `1`, so the integral is elementary.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6.lean#L48-L58
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6.lean#L48-L58

import Definitions.Def_Sendov_Common_Basic
import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_Degree6
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}

theorem Sendov.integral_six (α : ℝ) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 6 α t ^ ((((6 : ℕ) : ℝ) - 4) / 2))
      = 1 / 4 - 2 * c 6 α / 5 + A 6 α / 6 := by sorry
