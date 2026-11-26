-- Prove2me | Theorems.Thm_P2M_Sendov_rpow_le_rpow_exponent_ge__9a7132cbe0b0
-- name    : P2M_Sendov_rpow_le_rpow_exponent_ge__9a7132cbe0b0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:04.973822+00:00
-- url     : https://prove2.me/theorems/3d2752b2-8d8f-4966-95d1-b72bd456be3d
-- title:
--   P2 M Sendov rpow le rpow exponent ge  9a7132cbe0b0: P2 M Sendov rpow le rpow exponent ge  9a7132cbe0b0
-- statement:
--   `x ^ y ≤ x ^ z` for `0 ≤ x ≤ 1` and `0 < z ≤ y`, allowing `x = 0`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Batch.lean#L98-L102
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Batch.lean#L98-L102

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_Batch
set_option autoImplicit false
open Sendov
variable {α t : ℝ}
open MeasureTheory

theorem P2M_Sendov_rpow_le_rpow_exponent_ge__9a7132cbe0b0 {x y z : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz : 0 < z)
    (hzy : z ≤ y) : x ^ y ≤ x ^ z := by sorry

alias «Sendov».«rpow_le_rpow_exponent_ge'» := P2M_Sendov_rpow_le_rpow_exponent_ge__9a7132cbe0b0
