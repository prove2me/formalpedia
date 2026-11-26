-- Prove2me | Theorems.Thm_Sendov_B12_13_integral_lo
-- name    : Sendov.B12_13.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:07:04.9488+00:00
-- url     : https://prove2.me/theorems/107ad50f-bfdb-4661-89e0-ece86e7fa337
-- title:
--   B12 13: integral lo
-- statement:
--   The B12 13 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree12_13.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree12_13.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree12_13
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B12_13

theorem Sendov.B12_13.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 12 α t ^ 4)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 12 * (3 + α)) ^ 4) := by sorry
