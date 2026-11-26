-- Prove2me | Theorems.Thm_Sendov_B50_51_integral_lo
-- name    : Sendov.B50_51.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:24:15.259389+00:00
-- url     : https://prove2.me/theorems/f1891aee-f589-5f7b-bbba-3e0cd3ae5275
-- title:
--   B50 51: integral lo
-- statement:
--   The B50 51 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree50_51.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree50_51.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree50_51
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B50_51

theorem Sendov.B50_51.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 50 α t ^ 23)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 50 * (3 + α)) ^ 23) := by sorry
