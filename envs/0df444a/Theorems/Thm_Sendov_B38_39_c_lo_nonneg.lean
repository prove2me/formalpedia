-- Prove2me | Theorems.Thm_Sendov_B38_39_c_lo_nonneg
-- name    : Sendov.B38_39.c_lo_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:16:29.019731+00:00
-- url     : https://prove2.me/theorems/934595b7-0946-5075-a6c2-f786c5b49322
-- title:
--   B38 39: c lo nonneg
-- statement:
--   `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
--   which for `n₀ < 36` does not follow from `α ≤ 17`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree38_39.lean#L47-L51
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree38_39.lean#L47-L51

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree38_39
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B38_39

theorem Sendov.B38_39.c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 17) : 0 ≤ c 38 α := by sorry
