-- Prove2me | Theorems.Thm_Sendov_B64_69_integral_lo
-- name    : Sendov.B64_69.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:37:52.994908+00:00
-- url     : https://prove2.me/theorems/550a07cd-fd1c-5055-acf4-9d3e07b16566
-- title:
--   B64 69: integral lo
-- statement:
--   The B64 69 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree64_69.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree64_69.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree64_69
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B64_69

theorem Sendov.B64_69.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 64 α t ^ 30)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 64 * (3 + α)) ^ 30) := by sorry
