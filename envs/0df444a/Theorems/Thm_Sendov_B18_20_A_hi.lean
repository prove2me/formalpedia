-- Prove2me | Theorems.Thm_Sendov_B18_20_A_hi
-- name    : Sendov.B18_20.A_hi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:07:45.992999+00:00
-- url     : https://prove2.me/theorems/37ad5aaa-5787-56f1-b8b2-0a242df10205
-- title:
--   B18 20: A hi
-- statement:
--   The B18 20 construction uses the A hi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree18_20.lean#L36-L36
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree18_20.lean#L36-L36

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree18_20
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B18_20

theorem Sendov.B18_20.A_hi (α : ℝ) : A 20 α = 1 - 2 * α / 19 := by sorry
