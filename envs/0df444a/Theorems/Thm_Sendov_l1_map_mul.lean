-- Prove2me | Theorems.Thm_Sendov_l1_map_mul
-- name    : Sendov.l1_map_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:32.552943+00:00
-- url     : https://prove2.me/theorems/84f31008-d28a-5a02-8962-8d74245e7c6e
-- title:
--   Sendov: l1 map mul
-- statement:
--   The Sendov construction uses the l1 map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L177-L182
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L177-L182

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.l1_map_mul (c : ℤ) (q : List ℤ) : l1 (q.map (fun x => c * x)) = |c| * l1 q := by sorry
