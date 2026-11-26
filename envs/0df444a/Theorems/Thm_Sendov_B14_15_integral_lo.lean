-- Prove2me | Theorems.Thm_Sendov_B14_15_integral_lo
-- name    : Sendov.B14_15.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:07:18.361375+00:00
-- url     : https://prove2.me/theorems/6be25d9d-11e3-5848-a9de-e854290cdb3c
-- title:
--   B14 15: integral lo
-- statement:
--   The B14 15 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree14_15.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree14_15.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree14_15
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B14_15

theorem Sendov.B14_15.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 14 α t ^ 5)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 14 * (3 + α)) ^ 5) := by sorry
