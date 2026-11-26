-- Prove2me | Theorems.Thm_Sendov_B8_9_c_lo_nonneg
-- name    : Sendov.B8_9.c_lo_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:06:23.128814+00:00
-- url     : https://prove2.me/theorems/2a0b8fd6-3b7d-448c-8600-988c91244f44
-- title:
--   B8 9: c lo nonneg
-- statement:
--   `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
--   which for `n₀ < 36` does not follow from `α ≤ 17`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree8_9.lean#L47-L51
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree8_9.lean#L47-L51

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree8_9
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B8_9

theorem Sendov.B8_9.c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 4) : 0 ≤ c 8 α := by sorry
