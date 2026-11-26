-- Prove2me | Theorems.Thm_Sendov_B20_22_A_hi
-- name    : Sendov.B20_22.A_hi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:08:50.53401+00:00
-- url     : https://prove2.me/theorems/a373902f-bac9-5f3f-8b09-6516f6b55556
-- title:
--   B20 22: A hi
-- statement:
--   The B20 22 construction uses the A hi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20_22.lean#L36-L36
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20_22.lean#L36-L36

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree20_22
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B20_22

theorem Sendov.B20_22.A_hi (α : ℝ) : A 22 α = 1 - 2 * α / 21 := by sorry
