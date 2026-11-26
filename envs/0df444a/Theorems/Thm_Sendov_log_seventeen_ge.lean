-- Prove2me | Theorems.Thm_Sendov_log_seventeen_ge
-- name    : Sendov.log_seventeen_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:49:55.563026+00:00
-- url     : https://prove2.me/theorems/e357b0f2-de9d-57aa-9bcc-b95d9d155ac7
-- title:
--   Sendov: log seventeen ge
-- statement:
--   `2.83 ≤ log 17`, via `log 16 + log(17/16) ≥ 4 log 2 + 1/17`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Alpha17.lean#L72-L85
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Alpha17.lean#L72-L85

import Definitions.Def_Sendov_Reduction_Simplified
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_Sendov_Reduction_Alpha17
set_option autoImplicit false
open Sendov
open MeasureTheory Real

theorem Sendov.log_seventeen_ge : (2.83 : ℝ) ≤ Real.log 17 := by sorry
