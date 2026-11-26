-- Prove2me | Theorems.Thm_Sendov_M_twenty
-- name    : Sendov.M_twenty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:00:40.714841+00:00
-- url     : https://prove2.me/theorems/50733455-91dd-4223-9b46-e30987e6464d
-- title:
--   Sendov: M twenty
-- statement:
--   The Sendov construction uses the M twenty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20.lean#L34-L34
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20.lean#L34-L34

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20
set_option autoImplicit false
set_option maxRecDepth 8000
open Sendov
open MeasureTheory
variable {α : ℝ}

theorem Sendov.M_twenty : M 20 = 19 := by sorry
