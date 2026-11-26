-- Prove2me | Theorems.Thm_Sendov_B40_41_A_lo
-- name    : Sendov.B40_41.A_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:36:06.924035+00:00
-- url     : https://prove2.me/theorems/45ed454c-94b8-40c5-83e4-5d39a75c49ad
-- title:
--   B40 41: A lo
-- statement:
--   The B40 41 construction uses the A lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree40_41.lean#L34-L34
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree40_41.lean#L34-L34

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree40_41
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B40_41

theorem Sendov.B40_41.A_lo (α : ℝ) : A 40 α = 1 - 2 * α / 39 := by sorry
