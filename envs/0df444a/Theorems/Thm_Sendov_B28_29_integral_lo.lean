-- Prove2me | Theorems.Thm_Sendov_B28_29_integral_lo
-- name    : Sendov.B28_29.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:11:50.556328+00:00
-- url     : https://prove2.me/theorems/d87b4313-fece-504a-a1b0-7e085d85dd5b
-- title:
--   B28 29: integral lo
-- statement:
--   The B28 29 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree28_29.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree28_29.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree28_29
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B28_29

theorem Sendov.B28_29.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 28 α t ^ 12)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 28 * (3 + α)) ^ 12) := by sorry
