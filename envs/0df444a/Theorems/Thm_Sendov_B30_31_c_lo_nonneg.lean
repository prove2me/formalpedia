-- Prove2me | Theorems.Thm_Sendov_B30_31_c_lo_nonneg
-- name    : Sendov.B30_31.c_lo_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:12:12.998886+00:00
-- url     : https://prove2.me/theorems/1d83020d-c5c6-5d8f-9932-b8744b1f075a
-- title:
--   B30 31: c lo nonneg
-- statement:
--   `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
--   which for `n₀ < 36` does not follow from `α ≤ 17`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree30_31.lean#L47-L51
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree30_31.lean#L47-L51

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree30_31
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B30_31

theorem Sendov.B30_31.c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 15) : 0 ≤ c 30 α := by sorry
