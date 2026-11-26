-- Prove2me | Theorems.Thm_Sendov_integral_exp_mul
-- name    : Sendov.integral_exp_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:43:59.198869+00:00
-- url     : https://prove2.me/theorems/d19279bb-a3ee-5eaa-a81c-ccaafa5c90e2
-- title:
--   Sendov: integral exp mul
-- statement:
--   `∫ₐᵇ exp(ct) dt = (exp(cb) - exp(ca))/c`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/BetaBound.lean#L42-L47
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/BetaBound.lean#L42-L47

import Definitions.Def_Sendov_Reduction_Polar
import Definitions.Def_Sendov_Common_Sinh
import Definitions.Def_Sendov_Reduction_BetaBound
set_option autoImplicit false
open Sendov
open MeasureTheory Real
variable {α B c : ℝ}

theorem Sendov.integral_exp_mul (hc : c ≠ 0) (a b : ℝ) :
    (∫ t in a..b, exp (c * t)) = (exp (c * b) - exp (c * a)) / c := by sorry
