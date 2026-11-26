-- Prove2me | Theorems.Thm_Sendov_pevZ_map_mul
-- name    : Sendov.pevZ_map_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:05:01.129269+00:00
-- url     : https://prove2.me/theorems/557aacc5-67fc-5954-92bb-8b58ec6ae18f
-- title:
--   Sendov: pev Z map mul
-- statement:
--   The Sendov construction uses the pev Z map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L378-L382
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L378-L382

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.pevZ_map_mul (c : ℤ) (q : List ℤ) (b : ℤ) :
    pevZ (q.map (fun x => c * x)) b = c * pevZ q b := by sorry
