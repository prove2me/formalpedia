-- Prove2me | Theorems.Thm_TunnellMap_assemble_fiber_iff
-- name    : TunnellMap.assemble_fiber_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:41:04.900393+00:00
-- url     : https://prove2.me/theorems/a19e7b73-ba51-4855-a239-e8d92b42fddd
-- title:
--   Tunnell Map: assemble fiber iff
-- statement:
--   The Tunnell Map construction uses the assemble fiber iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Assembly.lean#L34-L44
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Assembly.lean#L34-L44

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_Assembly
set_option autoImplicit true
open TunnellMap
variable {E O A : Type*}

theorem TunnellMap.assemble_fiber_iff (even : E ≃ A) (odd : O ≃ A) (a : A)
    (x : E ⊕ O) :
    assemble even odd x = a ↔
      x = Sum.inl (even.symm a) ∨ x = Sum.inr (odd.symm a) := by sorry
