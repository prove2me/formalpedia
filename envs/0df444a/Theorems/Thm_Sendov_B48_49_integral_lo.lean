-- Prove2me | Theorems.Thm_Sendov_B48_49_integral_lo
-- name    : Sendov.B48_49.integral_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:23:00.664839+00:00
-- url     : https://prove2.me/theorems/aa0f45e1-72b7-574d-aa67-e39c25b08544
-- title:
--   B48 49: integral lo
-- statement:
--   The B48 49 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree48_49.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree48_49.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree48_49
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B48_49

theorem Sendov.B48_49.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 48 α t ^ 22)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 48 * (3 + α)) ^ 22) := by sorry
