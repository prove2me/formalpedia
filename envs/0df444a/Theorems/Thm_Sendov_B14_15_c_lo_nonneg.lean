-- Prove2me | Theorems.Thm_Sendov_B14_15_c_lo_nonneg
-- name    : Sendov.B14_15.c_lo_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:07:14.643175+00:00
-- url     : https://prove2.me/theorems/f7754eb1-a848-575f-a786-433125c2000e
-- title:
--   B14 15: c lo nonneg
-- statement:
--   `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
--   which for `n₀ < 36` does not follow from `α ≤ 17`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree14_15.lean#L47-L51
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree14_15.lean#L47-L51

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree14_15
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B14_15

theorem Sendov.B14_15.c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 7) : 0 ≤ c 14 α := by sorry
