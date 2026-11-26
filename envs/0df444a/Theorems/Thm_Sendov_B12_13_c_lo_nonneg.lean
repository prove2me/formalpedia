-- Prove2me | Theorems.Thm_Sendov_B12_13_c_lo_nonneg
-- name    : Sendov.B12_13.c_lo_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:06:54.248852+00:00
-- url     : https://prove2.me/theorems/6f372585-8212-4682-8987-a43d494087f8
-- title:
--   B12 13: c lo nonneg
-- statement:
--   `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
--   which for `n₀ < 36` does not follow from `α ≤ 17`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree12_13.lean#L47-L51
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree12_13.lean#L47-L51

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree12_13
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B12_13

theorem Sendov.B12_13.c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 6) : 0 ≤ c 12 α := by sorry
