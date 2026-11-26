-- Prove2me | Theorems.Thm_Sendov_B32_33_integral_lo
-- name    : Sendov.B32_33.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:14:15.836263+00:00
-- url     : https://prove2.me/theorems/7171b052-bfec-46e7-8832-a263f6b9d5f0
-- title:
--   B32 33: integral lo
-- statement:
--   The B32 33 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree32_33.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree32_33.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree32_33
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B32_33

theorem Sendov.B32_33.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 32 α t ^ 14)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 32 * (3 + α)) ^ 14) := by sorry
