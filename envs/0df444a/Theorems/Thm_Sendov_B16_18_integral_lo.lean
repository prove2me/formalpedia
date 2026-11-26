-- Prove2me | Theorems.Thm_Sendov_B16_18_integral_lo
-- name    : Sendov.B16_18.integral_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:07:40.914802+00:00
-- url     : https://prove2.me/theorems/4dadd1aa-93b5-4db3-8484-31d764b577b0
-- title:
--   B16 18: integral lo
-- statement:
--   The B16 18 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree16_18.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree16_18.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree16_18
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B16_18

theorem Sendov.B16_18.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 16 α t ^ 6)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 16 * (3 + α)) ^ 6) := by sorry
