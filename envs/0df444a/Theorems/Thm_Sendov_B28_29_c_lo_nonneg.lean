-- Prove2me | Theorems.Thm_Sendov_B28_29_c_lo_nonneg
-- name    : Sendov.B28_29.c_lo_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:11:50.656306+00:00
-- url     : https://prove2.me/theorems/7c0ddab8-3f72-57b4-9423-b08814aaaeea
-- title:
--   B28 29: c lo nonneg
-- statement:
--   `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
--   which for `n₀ < 36` does not follow from `α ≤ 17`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree28_29.lean#L47-L51
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree28_29.lean#L47-L51

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree28_29
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B28_29

theorem Sendov.B28_29.c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 14) : 0 ≤ c 28 α := by sorry
