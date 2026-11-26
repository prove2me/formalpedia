-- Prove2me | Theorems.Thm_Sendov_B26_27_integral_lo
-- name    : Sendov.B26_27.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:11:02.351128+00:00
-- url     : https://prove2.me/theorems/7255861f-c9dd-4e84-a01b-9720d6d98d57
-- title:
--   B26 27: integral lo
-- statement:
--   The B26 27 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree26_27.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree26_27.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree26_27
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B26_27

theorem Sendov.B26_27.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 26 α t ^ 11)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 26 * (3 + α)) ^ 11) := by sorry
