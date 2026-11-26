-- Prove2me | Theorems.Thm_Sendov_beta_lt_two
-- name    : Sendov.beta_lt_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:44:19.39646+00:00
-- url     : https://prove2.me/theorems/603a26eb-b003-4d77-89e9-a6709125b72b
-- title:
--   Sendov: beta lt two
-- statement:
--   `(lt)` forces `B < 2`: otherwise the integrand never exceeds `e^{-α} < 1`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/BetaBound.lean#L88-L105
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/BetaBound.lean#L88-L105

import Definitions.Def_Sendov_Reduction_Polar
import Definitions.Def_Sendov_Common_Sinh
import Definitions.Def_Sendov_Reduction_BetaBound
set_option autoImplicit false
open Sendov
open MeasureTheory Real
variable {α B c : ℝ}

theorem Sendov.beta_lt_two (hα : 0 < α)
    (hlt : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t))) : B < 2 := by sorry
