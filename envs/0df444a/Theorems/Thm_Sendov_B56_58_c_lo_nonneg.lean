-- Prove2me | Theorems.Thm_Sendov_B56_58_c_lo_nonneg
-- name    : Sendov.B56_58.c_lo_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:30:23.581029+00:00
-- url     : https://prove2.me/theorems/e0feb880-4586-559e-a873-2c5166dddf0a
-- title:
--   B56 58: c lo nonneg
-- statement:
--   `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
--   which for `n₀ < 36` does not follow from `α ≤ 17`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree56_58.lean#L47-L51
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree56_58.lean#L47-L51

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree56_58
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B56_58

theorem Sendov.B56_58.c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 17) : 0 ≤ c 56 α := by sorry
