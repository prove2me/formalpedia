-- Prove2me | Theorems.Thm_Sendov_B36_37_A_hi
-- name    : Sendov.B36_37.A_hi
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:14:59.602807+00:00
-- url     : https://prove2.me/theorems/f106b866-e229-43a7-b434-7614da100ea0
-- title:
--   B36 37: A hi
-- statement:
--   The B36 37 construction uses the A hi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree36_37.lean#L36-L36
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree36_37.lean#L36-L36

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree36_37
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B36_37

theorem Sendov.B36_37.A_hi (α : ℝ) : A 37 α = 1 - 2 * α / 36 := by sorry
