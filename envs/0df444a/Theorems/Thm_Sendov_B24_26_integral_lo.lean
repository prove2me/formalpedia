-- Prove2me | Theorems.Thm_Sendov_B24_26_integral_lo
-- name    : Sendov.B24_26.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:09:59.339946+00:00
-- url     : https://prove2.me/theorems/b790e44a-37a0-4dc7-8b94-8ba0d6e93faa
-- title:
--   B24 26: integral lo
-- statement:
--   The B24 26 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree24_26.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree24_26.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree24_26
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B24_26

theorem Sendov.B24_26.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 24 α t ^ 10)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 24 * (3 + α)) ^ 10) := by sorry
