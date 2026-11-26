-- Prove2me | Theorems.Thm_Sendov_l1_cons
-- name    : Sendov.l1_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:01:45.986446+00:00
-- url     : https://prove2.me/theorems/1963a01c-82d1-5d55-a6c7-f205a0117e89
-- title:
--   Sendov: l1 cons
-- statement:
--   The Sendov construction uses the l1 cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L148-L148
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L148-L148

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.l1_cons (a : ℤ) (p : List ℤ) : l1 (a :: p) = |a| + l1 p := by sorry

attribute [defeq] Sendov.l1_cons
