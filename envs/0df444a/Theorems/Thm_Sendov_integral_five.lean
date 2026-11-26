-- Prove2me | Theorems.Thm_Sendov_integral_five
-- name    : Sendov.integral_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:57:04.827807+00:00
-- url     : https://prove2.me/theorems/a7fd1d8f-5c97-581a-8413-117e110c613d
-- title:
--   Sendov: integral five
-- statement:
--   The odd-degree bound in degree five, with the tangent line taken at `q = 1/9`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree5.lean#L67-L80
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree5.lean#L67-L80

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Degree5
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}

theorem Sendov.integral_five (hfeas : c 5 α ^ 2 ≤ A 5 α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 5 α t ^ ((((5 : ℕ) : ℝ) - 4) / 2))
      ≤ 3 / 2 * (1 / 4 - 2 * c 5 α / 5 + A 5 α / 6) + 1 / 24 := by sorry
