-- Prove2me | Theorems.Thm_Sendov_B24_26_A_hi
-- name    : Sendov.B24_26.A_hi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:09:43.95863+00:00
-- url     : https://prove2.me/theorems/7ab5fac3-417e-5971-9ebd-73bd1a6cbf35
-- title:
--   B24 26: A hi
-- statement:
--   The B24 26 construction uses the A hi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree24_26.lean#L36-L36
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree24_26.lean#L36-L36

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree24_26
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B24_26

theorem Sendov.B24_26.A_hi (α : ℝ) : A 26 α = 1 - 2 * α / 25 := by sorry
