-- Prove2me | Theorems.Thm_Sendov_B58_60_integral_lo
-- name    : Sendov.B58_60.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:32:57.718656+00:00
-- url     : https://prove2.me/theorems/10593a74-42c4-529c-97dc-4eb427fde91b
-- title:
--   B58 60: integral lo
-- statement:
--   The B58 60 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree58_60.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree58_60.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree58_60
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B58_60

theorem Sendov.B58_60.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 58 α t ^ 27)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 58 * (3 + α)) ^ 27) := by sorry
