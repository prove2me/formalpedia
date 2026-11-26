-- Prove2me | Theorems.Thm_Sendov_B64_69_c_lo_nonneg
-- name    : Sendov.B64_69.c_lo_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:37:40.324289+00:00
-- url     : https://prove2.me/theorems/6d960ce7-7c93-4467-9481-62aa555440c6
-- title:
--   B64 69: c lo nonneg
-- statement:
--   `c` is nonnegative at `n₀` on the batch's `α`-range.  This replaces feasibility at `n₀`,
--   which for `n₀ < 36` does not follow from `α ≤ 17`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree64_69.lean#L47-L51
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree64_69.lean#L47-L51

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree64_69
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B64_69

theorem Sendov.B64_69.c_lo_nonneg {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 17) : 0 ≤ c 64 α := by sorry
