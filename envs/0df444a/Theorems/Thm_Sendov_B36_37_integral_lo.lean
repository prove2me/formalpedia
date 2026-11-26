-- Prove2me | Theorems.Thm_Sendov_B36_37_integral_lo
-- name    : Sendov.B36_37.integral_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:15:21.36742+00:00
-- url     : https://prove2.me/theorems/a87e8a07-6a47-4e37-9081-db295917106f
-- title:
--   B36 37: integral lo
-- statement:
--   The B36 37 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree36_37.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree36_37.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree36_37
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B36_37

theorem Sendov.B36_37.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 36 α t ^ 16)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 36 * (3 + α)) ^ 16) := by sorry
