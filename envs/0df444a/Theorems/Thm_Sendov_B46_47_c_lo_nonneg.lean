-- Prove2me | Theorems.Thm_Sendov_B46_47_c_lo_nonneg
-- name    : Sendov.B46_47.c_lo_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:21:18.627796+00:00
-- url     : https://prove2.me/theorems/f3c245bd-5982-42fd-8d0f-1d3b8efbbd42
-- title:
--   B46 47: c lo nonneg
-- statement:
--   `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
--   which for `n₀ < 36` does not follow from `α ≤ 17`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree46_47.lean#L47-L51
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree46_47.lean#L47-L51

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree46_47
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B46_47

theorem Sendov.B46_47.c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 17) : 0 ≤ c 46 α := by sorry
