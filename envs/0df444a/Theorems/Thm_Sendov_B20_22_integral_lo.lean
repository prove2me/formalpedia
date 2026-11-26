-- Prove2me | Theorems.Thm_Sendov_B20_22_integral_lo
-- name    : Sendov.B20_22.integral_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:09:13.794124+00:00
-- url     : https://prove2.me/theorems/ada6823e-3d9b-4b04-8634-dd519f868c45
-- title:
--   B20 22: integral lo
-- statement:
--   The B20 22 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20_22.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20_22.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree20_22
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B20_22

theorem Sendov.B20_22.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 20 α t ^ 8)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 20 * (3 + α)) ^ 8) := by sorry
