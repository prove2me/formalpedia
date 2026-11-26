-- Prove2me | Theorems.Thm_Sendov_integral_exp_eq
-- name    : Sendov.integral_exp_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:44:02.543524+00:00
-- url     : https://prove2.me/theorems/c5e1dc82-9dab-42ef-bd7f-324754ce7cd8
-- title:
--   Sendov: integral exp eq
-- statement:
--   The closed form of the integral in `(lt)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/BetaBound.lean#L50-L68
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/BetaBound.lean#L50-L68

import Definitions.Def_Sendov_Reduction_Polar
import Definitions.Def_Sendov_Common_Sinh
import Definitions.Def_Sendov_Reduction_BetaBound
set_option autoImplicit false
open Sendov
open MeasureTheory Real
variable {α B c : ℝ}

theorem Sendov.integral_exp_eq (hα : 0 < α) (hB : B < 2) :
    (∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t)))
      = exp (-(α * B / 2)) * (sinh (α * (2 - B) / 2) / (α * (2 - B) / 2)) := by sorry
