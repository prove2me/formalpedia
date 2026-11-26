-- Prove2me | Theorems.Thm_Sendov_B30_31_integral_lo
-- name    : Sendov.B30_31.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:12:21.059392+00:00
-- url     : https://prove2.me/theorems/eb241987-2af9-468c-baa6-dcb834ff8597
-- title:
--   B30 31: integral lo
-- statement:
--   The B30 31 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree30_31.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree30_31.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree30_31
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B30_31

theorem Sendov.B30_31.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 30 α t ^ 13)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 30 * (3 + α)) ^ 13) := by sorry
