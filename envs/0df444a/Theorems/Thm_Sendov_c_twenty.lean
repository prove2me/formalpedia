-- Prove2me | Theorems.Thm_Sendov_c_twenty
-- name    : Sendov.c_twenty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:00:46.579194+00:00
-- url     : https://prove2.me/theorems/5f19d7b9-c150-5fe3-9609-2bc535c95ec6
-- title:
--   Sendov: c twenty
-- statement:
--   The Sendov construction uses the c twenty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20.lean#L41-L44
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20.lean#L41-L44

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20
set_option autoImplicit false
set_option maxRecDepth 8000
open Sendov
open MeasureTheory
variable {α : ℝ}

theorem Sendov.c_twenty (α : ℝ) : c 20 α = 1 - α / 19 - α / (2 * (3 + α)) := by sorry
