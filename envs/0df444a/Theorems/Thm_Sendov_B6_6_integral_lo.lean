-- Prove2me | Theorems.Thm_Sendov_B6_6_integral_lo
-- name    : Sendov.B6_6.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:05:58.933031+00:00
-- url     : https://prove2.me/theorems/6ba1d26f-1584-5844-8b9f-fef8293a3e80
-- title:
--   B6 6: integral lo
-- statement:
--   The B6 6 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6_6.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6_6.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree6_6
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B6_6

theorem Sendov.B6_6.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 6 α t ^ 1)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 6 * (3 + α)) ^ 1) := by sorry
