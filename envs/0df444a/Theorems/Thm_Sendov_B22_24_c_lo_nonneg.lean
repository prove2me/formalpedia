-- Prove2me | Theorems.Thm_Sendov_B22_24_c_lo_nonneg
-- name    : Sendov.B22_24.c_lo_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:09:26.318478+00:00
-- url     : https://prove2.me/theorems/fb1a0416-01be-5792-9245-8e581092e71f
-- title:
--   B22 24: c lo nonneg
-- statement:
--   `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
--   which for `n₀ < 36` does not follow from `α ≤ 17`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree22_24.lean#L47-L51
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree22_24.lean#L47-L51

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree22_24
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B22_24

theorem Sendov.B22_24.c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 23 / 2) : 0 ≤ c 22 α := by sorry
