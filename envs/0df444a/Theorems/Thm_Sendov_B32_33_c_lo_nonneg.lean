-- Prove2me | Theorems.Thm_Sendov_B32_33_c_lo_nonneg
-- name    : Sendov.B32_33.c_lo_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:13:57.68291+00:00
-- url     : https://prove2.me/theorems/f7803919-9375-5351-b064-ce36970ae1be
-- title:
--   B32 33: c lo nonneg
-- statement:
--   `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
--   which for `n₀ < 36` does not follow from `α ≤ 17`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree32_33.lean#L47-L51
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree32_33.lean#L47-L51

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree32_33
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B32_33

theorem Sendov.B32_33.c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 16) : 0 ≤ c 32 α := by sorry
