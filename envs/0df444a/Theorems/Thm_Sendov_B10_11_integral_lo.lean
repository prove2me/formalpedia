-- Prove2me | Theorems.Thm_Sendov_B10_11_integral_lo
-- name    : Sendov.B10_11.integral_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:06:40.529191+00:00
-- url     : https://prove2.me/theorems/0bcbb4ee-5940-4f34-a75b-20f92c0a5a55
-- title:
--   B10 11: integral lo
-- statement:
--   The B10 11 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree10_11.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree10_11.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree10_11
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B10_11

theorem Sendov.B10_11.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 10 α t ^ 3)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 10 * (3 + α)) ^ 3) := by sorry
