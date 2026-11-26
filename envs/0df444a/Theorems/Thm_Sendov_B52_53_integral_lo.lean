-- Prove2me | Theorems.Thm_Sendov_B52_53_integral_lo
-- name    : Sendov.B52_53.integral_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:26:03.753389+00:00
-- url     : https://prove2.me/theorems/3383edd2-c666-51b8-a954-973ad5d81cc0
-- title:
--   B52 53: integral lo
-- statement:
--   The B52 53 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree52_53.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree52_53.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree52_53
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B52_53

theorem Sendov.B52_53.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 52 α t ^ 24)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 52 * (3 + α)) ^ 24) := by sorry
