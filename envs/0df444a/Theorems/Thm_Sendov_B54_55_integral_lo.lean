-- Prove2me | Theorems.Thm_Sendov_B54_55_integral_lo
-- name    : Sendov.B54_55.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:27:41.573137+00:00
-- url     : https://prove2.me/theorems/10fc348d-ce88-5ff8-ae8d-7fcf6c525b4c
-- title:
--   B54 55: integral lo
-- statement:
--   The B54 55 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree54_55.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree54_55.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree54_55
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B54_55

theorem Sendov.B54_55.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 54 α t ^ 25)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 54 * (3 + α)) ^ 25) := by sorry
