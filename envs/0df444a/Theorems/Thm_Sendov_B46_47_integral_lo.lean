-- Prove2me | Theorems.Thm_Sendov_B46_47_integral_lo
-- name    : Sendov.B46_47.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:21:21.118794+00:00
-- url     : https://prove2.me/theorems/c19e499a-3cca-4583-bea4-15e72fadbdfc
-- title:
--   B46 47: integral lo
-- statement:
--   The B46 47 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree46_47.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree46_47.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree46_47
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B46_47

theorem Sendov.B46_47.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 46 α t ^ 21)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 46 * (3 + α)) ^ 21) := by sorry
