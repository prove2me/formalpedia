-- Prove2me | Theorems.Thm_Sendov_B38_39_integral_lo
-- name    : Sendov.B38_39.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:16:41.682787+00:00
-- url     : https://prove2.me/theorems/530ae2a4-d142-4715-90d8-e6a67e73bc4b
-- title:
--   B38 39: integral lo
-- statement:
--   The B38 39 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree38_39.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree38_39.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree38_39
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B38_39

theorem Sendov.B38_39.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 38 α t ^ 17)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 38 * (3 + α)) ^ 17) := by sorry
