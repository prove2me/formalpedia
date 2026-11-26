-- Prove2me | Theorems.Thm_Sendov_abs_le_l1
-- name    : Sendov.abs_le_l1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:35.492291+00:00
-- url     : https://prove2.me/theorems/744ebc9f-b30e-48f7-ae83-e284c157632e
-- title:
--   Sendov: abs le l1
-- statement:
--   The Sendov construction uses the abs le l1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L155-L163
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L155-L163

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.abs_le_l1 : ∀ (p : List ℤ) (a : ℤ), a ∈ p → |a| ≤ l1 p := by sorry
