-- Prove2me | Theorems.Thm_Sendov_B8_9_integral_lo
-- name    : Sendov.B8_9.integral_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:06:14.974522+00:00
-- url     : https://prove2.me/theorems/98a08a6e-6dad-58cf-8f5f-b16bed3c120d
-- title:
--   B8 9: integral lo
-- statement:
--   The B8 9 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree8_9.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree8_9.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree8_9
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B8_9

theorem Sendov.B8_9.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 8 α t ^ 2)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 8 * (3 + α)) ^ 2) := by sorry
