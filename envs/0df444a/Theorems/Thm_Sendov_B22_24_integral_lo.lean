-- Prove2me | Theorems.Thm_Sendov_B22_24_integral_lo
-- name    : Sendov.B22_24.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:09:35.327974+00:00
-- url     : https://prove2.me/theorems/5401f5dc-b60f-434b-9eba-eefebe0a411a
-- title:
--   B22 24: integral lo
-- statement:
--   The B22 24 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree22_24.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree22_24.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree22_24
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B22_24

theorem Sendov.B22_24.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 22 α t ^ 9)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 22 * (3 + α)) ^ 9) := by sorry
