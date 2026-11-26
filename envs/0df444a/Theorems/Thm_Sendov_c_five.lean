-- Prove2me | Theorems.Thm_Sendov_c_five
-- name    : Sendov.c_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:54.392141+00:00
-- url     : https://prove2.me/theorems/dc3c3fb2-321d-5096-9f80-3c8e776adaac
-- title:
--   Sendov: c five
-- statement:
--   The Sendov construction uses the c five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree5.lean#L55-L58
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree5.lean#L55-L58

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Degree5
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}

theorem Sendov.c_five (α : ℝ) : c 5 α = 1 - α / 4 - α / (2 * (3 + α)) := by sorry
