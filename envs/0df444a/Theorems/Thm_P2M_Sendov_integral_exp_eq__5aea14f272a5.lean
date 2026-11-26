-- Prove2me | Theorems.Thm_P2M_Sendov_integral_exp_eq__5aea14f272a5
-- name    : P2M_Sendov_integral_exp_eq__5aea14f272a5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:44:19.554566+00:00
-- url     : https://prove2.me/theorems/fbeaa81c-f15a-455f-bd00-4ab447c0e911
-- title:
--   P2 M Sendov integral exp eq  5aea14f272a5: P2 M Sendov integral exp eq  5aea14f272a5
-- statement:
--   The same integral, in the form the logarithmic half of `(beta-bound)` uses.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/BetaBound.lean#L71-L85
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/BetaBound.lean#L71-L85

import Definitions.Def_Sendov_Reduction_Polar
import Definitions.Def_Sendov_Common_Sinh
import Definitions.Def_Sendov_Reduction_BetaBound
set_option autoImplicit false
open Sendov
open MeasureTheory Real
variable {α B c : ℝ}

theorem P2M_Sendov_integral_exp_eq__5aea14f272a5 (hα : 0 < α) (hB : B < 2) :
    (∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t)))
      = (exp (α * (1 - B)) - exp (-α)) / (α * (2 - B)) := by sorry

alias «Sendov».«integral_exp_eq'» := P2M_Sendov_integral_exp_eq__5aea14f272a5
