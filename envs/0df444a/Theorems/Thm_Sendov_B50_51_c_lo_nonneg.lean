-- Prove2me | Theorems.Thm_Sendov_B50_51_c_lo_nonneg
-- name    : Sendov.B50_51.c_lo_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:24:18.908233+00:00
-- url     : https://prove2.me/theorems/ac058b5c-f678-43d1-94de-d2b6e035e36c
-- title:
--   B50 51: c lo nonneg
-- statement:
--   `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
--   which for `n₀ < 36` does not follow from `α ≤ 17`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree50_51.lean#L47-L51
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree50_51.lean#L47-L51

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree50_51
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B50_51

theorem Sendov.B50_51.c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 17) : 0 ≤ c 50 α := by sorry
