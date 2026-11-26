-- Prove2me | Theorems.Thm_Sendov_B70_79_integral_lo
-- name    : Sendov.B70_79.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:42:14.715889+00:00
-- url     : https://prove2.me/theorems/43c4b968-2890-4f39-9900-339b8af25db5
-- title:
--   B70 79: integral lo
-- statement:
--   The B70 79 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree70_79.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree70_79.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree70_79
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B70_79

theorem Sendov.B70_79.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 70 α t ^ 33)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 70 * (3 + α)) ^ 33) := by sorry
