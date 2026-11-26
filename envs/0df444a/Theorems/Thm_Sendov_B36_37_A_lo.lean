-- Prove2me | Theorems.Thm_Sendov_B36_37_A_lo
-- name    : Sendov.B36_37.A_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:33:56.770895+00:00
-- url     : https://prove2.me/theorems/7d592946-9b7d-5ca0-a217-f6d3f20dd369
-- title:
--   B36 37: A lo
-- statement:
--   The B36 37 construction uses the A lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree36_37.lean#L34-L34
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree36_37.lean#L34-L34

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree36_37
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B36_37

theorem Sendov.B36_37.A_lo (α : ℝ) : A 36 α = 1 - 2 * α / 35 := by sorry
