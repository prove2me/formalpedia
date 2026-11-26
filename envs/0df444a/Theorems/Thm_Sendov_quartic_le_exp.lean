-- Prove2me | Theorems.Thm_Sendov_quartic_le_exp
-- name    : Sendov.quartic_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:50:12.752841+00:00
-- url     : https://prove2.me/theorems/76740639-0e9c-4b2e-8286-3815da5df907
-- title:
--   Sendov: quartic le exp
-- statement:
--   Four terms of the exponential series.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Alpha17.lean#L47-L50
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Alpha17.lean#L47-L50

import Definitions.Def_Sendov_Reduction_Simplified
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Sendov_Reduction_Alpha17
set_option autoImplicit false
open Sendov
open MeasureTheory Real

theorem Sendov.quartic_le_exp {z : ℝ} (hz : 0 ≤ z) : 1 + z + z ^ 2 / 2 + z ^ 3 / 6 ≤ exp z := by sorry
