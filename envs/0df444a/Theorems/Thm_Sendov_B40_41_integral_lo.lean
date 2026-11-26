-- Prove2me | Theorems.Thm_Sendov_B40_41_integral_lo
-- name    : Sendov.B40_41.integral_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:18:02.805172+00:00
-- url     : https://prove2.me/theorems/6291eebc-26ab-5b79-93e7-6ac506416cb7
-- title:
--   B40 41: integral lo
-- statement:
--   The B40 41 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree40_41.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree40_41.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree40_41
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B40_41

theorem Sendov.B40_41.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 40 α t ^ 18)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 40 * (3 + α)) ^ 18) := by sorry
