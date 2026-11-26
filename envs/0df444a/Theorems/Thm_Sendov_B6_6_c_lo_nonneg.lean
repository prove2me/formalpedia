-- Prove2me | Theorems.Thm_Sendov_B6_6_c_lo_nonneg
-- name    : Sendov.B6_6.c_lo_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:05:52.292635+00:00
-- url     : https://prove2.me/theorems/da0f45ed-0ace-5f64-bdeb-efa34f4fecd3
-- title:
--   B6 6: c lo nonneg
-- statement:
--   `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
--   which for `n₀ < 36` does not follow from `α ≤ 17`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6_6.lean#L47-L51
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6_6.lean#L47-L51

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree6_6
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B6_6

theorem Sendov.B6_6.c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 5 / 2) : 0 ≤ c 6 α := by sorry
