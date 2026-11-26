-- Prove2me | Theorems.Thm_Sendov_B60_63_integral_lo
-- name    : Sendov.B60_63.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:35:42.42157+00:00
-- url     : https://prove2.me/theorems/0f57b21b-2668-4119-8080-000d093dcaf3
-- title:
--   B60 63: integral lo
-- statement:
--   The B60 63 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree60_63.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree60_63.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree60_63
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B60_63

theorem Sendov.B60_63.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 60 α t ^ 28)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 60 * (3 + α)) ^ 28) := by sorry
