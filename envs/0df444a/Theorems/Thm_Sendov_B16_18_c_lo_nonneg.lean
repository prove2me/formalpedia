-- Prove2me | Theorems.Thm_Sendov_B16_18_c_lo_nonneg
-- name    : Sendov.B16_18.c_lo_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:07:34.443119+00:00
-- url     : https://prove2.me/theorems/a4fb3712-86b3-4160-8984-e20404224f29
-- title:
--   B16 18: c lo nonneg
-- statement:
--   `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
--   which for `n₀ < 36` does not follow from `α ≤ 17`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree16_18.lean#L47-L51
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree16_18.lean#L47-L51

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree16_18
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B16_18

theorem Sendov.B16_18.c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 17 / 2) : 0 ≤ c 16 α := by sorry
