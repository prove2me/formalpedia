-- Prove2me | Theorems.Thm_Sendov_log_le_alpha_mul
-- name    : Sendov.log_le_alpha_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T19:00:29.398815+00:00
-- url     : https://prove2.me/theorems/b0d7ea4a-d33b-55e1-8f60-888e30c068c5
-- title:
--   Sendov: log le alpha mul
-- statement:
--   **The logarithmic half of `(beta-bound)`:** `log α ≤ α(1 - β(1))`.  From `(lt)`,
--   `e^{α(1-B)} ≥ α(2-B) + e^{-α} > α`, since `B ≤ 1` makes `2 - B ≥ 1`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/BetaBound.lean#L140-L153
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/BetaBound.lean#L140-L153

import Definitions.Def_Sendov_Reduction_Polar
import Definitions.Def_Sendov_Common_Sinh
import Definitions.Def_Sendov_Reduction_BetaBound
set_option autoImplicit false
open Sendov
open MeasureTheory Real
variable {α B c : ℝ}

theorem Sendov.log_le_alpha_mul (hα : 0 < α) (hB1 : B ≤ 1)
    (hlt : 1 ≤ ∫ t in (0 : ℝ)..1, exp (α * (-1 + (2 - B) * t))) :
    Real.log α ≤ α * (1 - B) := by sorry
