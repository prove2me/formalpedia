-- Prove2me | Theorems.Thm_Sendov_B56_58_integral_lo
-- name    : Sendov.B56_58.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:30:25.896022+00:00
-- url     : https://prove2.me/theorems/e7cbc1af-0d31-5844-ba7e-934f6d8ccef3
-- title:
--   B56 58: integral lo
-- statement:
--   The B56 58 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree56_58.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree56_58.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree56_58
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B56_58

theorem Sendov.B56_58.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 56 α t ^ 26)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 56 * (3 + α)) ^ 26) := by sorry
