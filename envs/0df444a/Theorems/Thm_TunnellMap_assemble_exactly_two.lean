-- Prove2me | Theorems.Thm_TunnellMap_assemble_exactly_two
-- name    : TunnellMap.assemble_exactly_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:54.008461+00:00
-- url     : https://prove2.me/theorems/3e58dbc7-19bf-489d-833e-741ed34e2ab3
-- title:
--   Tunnell Map: assemble exactly two
-- statement:
--   The Tunnell Map construction uses the assemble exactly two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Assembly.lean#L53-L63
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Assembly.lean#L53-L63

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_Assembly
set_option autoImplicit true
open TunnellMap
variable {E O A : Type*}

theorem TunnellMap.assemble_exactly_two (even : E ≃ A) (odd : O ≃ A) (a : A) :
    ∃ x₁ x₂,
      x₁ ≠ x₂ ∧
      assemble even odd x₁ = a ∧
      assemble even odd x₂ = a ∧
      ∀ x, assemble even odd x = a ↔ x = x₁ ∨ x = x₂ := by sorry
