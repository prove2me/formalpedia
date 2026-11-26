-- Prove2me | Theorems.Thm_Sendov_B18_20_integral_lo
-- name    : Sendov.B18_20.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:07:50.702654+00:00
-- url     : https://prove2.me/theorems/ab29fe3e-474d-5677-a7a3-15c61a41e0be
-- title:
--   B18 20: integral lo
-- statement:
--   The B18 20 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree18_20.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree18_20.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree18_20
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B18_20

theorem Sendov.B18_20.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 18 α t ^ 7)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 18 * (3 + α)) ^ 7) := by sorry
