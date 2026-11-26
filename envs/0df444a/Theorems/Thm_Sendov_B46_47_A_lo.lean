-- Prove2me | Theorems.Thm_Sendov_B46_47_A_lo
-- name    : Sendov.B46_47.A_lo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:38:49.415719+00:00
-- url     : https://prove2.me/theorems/4dad0fde-026e-465c-b2e2-ac89d60de1fc
-- title:
--   B46 47: A lo
-- statement:
--   The B46 47 construction uses the A lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree46_47.lean#L34-L34
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree46_47.lean#L34-L34

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree46_47
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B46_47

theorem Sendov.B46_47.A_lo (α : ℝ) : A 46 α = 1 - 2 * α / 45 := by sorry
