-- Prove2me | Theorems.Thm_Sendov_l1_nonneg
-- name    : Sendov.l1_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:02:46.323309+00:00
-- url     : https://prove2.me/theorems/bfff4fc5-fe0e-4868-bac1-c8112849b92d
-- title:
--   Sendov: l1 nonneg
-- statement:
--   The Sendov construction uses the l1 nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L150-L153
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L150-L153

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.l1_nonneg (p : List ℤ) : 0 ≤ l1 p := by sorry
