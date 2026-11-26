-- Prove2me | Theorems.Thm_Sendov_B80_100_integral_lo
-- name    : Sendov.B80_100.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:00:34.18183+00:00
-- url     : https://prove2.me/theorems/feea19f5-d228-52c6-954b-f1acc963cee8
-- title:
--   B80 100: integral lo
-- statement:
--   The B80 100 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree80_100.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree80_100.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree80_100
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B80_100

theorem Sendov.B80_100.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 80 α t ^ 38)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 80 * (3 + α)) ^ 38) := by sorry
