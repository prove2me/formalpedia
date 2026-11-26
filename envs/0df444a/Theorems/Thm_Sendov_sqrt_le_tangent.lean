-- Prove2me | Theorems.Thm_Sendov_sqrt_le_tangent
-- name    : Sendov.sqrt_le_tangent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:55:56.676113+00:00
-- url     : https://prove2.me/theorems/b0c60065-b475-594e-bee9-09ff4c022bff
-- title:
--   Sendov: sqrt le tangent
-- statement:
--   The tangent line to `√·` at `q = w²`: `√q ≤ q/(2w) + w/2`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/OddBound.lean#L39-L42
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/OddBound.lean#L39-L42

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_OddBound
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {α q w : ℝ}

theorem Sendov.sqrt_le_tangent (hq : 0 ≤ q) (hw : 0 < w) : Real.sqrt q ≤ q / (2 * w) + w / 2 := by sorry
