-- Prove2me | Theorems.Thm_Sendov_B40_41_A_hi
-- name    : Sendov.B40_41.A_hi
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:17:40.897717+00:00
-- url     : https://prove2.me/theorems/be610662-502e-5f7d-b8a1-4247c10fe5dc
-- title:
--   B40 41: A hi
-- statement:
--   The B40 41 construction uses the A hi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree40_41.lean#L36-L36
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree40_41.lean#L36-L36

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree40_41
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B40_41

theorem Sendov.B40_41.A_hi (α : ℝ) : A 41 α = 1 - 2 * α / 40 := by sorry
