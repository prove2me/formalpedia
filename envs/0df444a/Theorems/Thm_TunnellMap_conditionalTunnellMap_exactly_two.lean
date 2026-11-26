-- Prove2me | Theorems.Thm_TunnellMap_conditionalTunnellMap_exactly_two
-- name    : TunnellMap.conditionalTunnellMap_exactly_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:49:57.243851+00:00
-- url     : https://prove2.me/theorems/fae5bffe-bb3d-529e-890e-b741e4167072
-- title:
--   Tunnell Map: conditional Tunnell Map exactly two
-- statement:
--   The Tunnell Map construction uses the conditional Tunnell Map exactly two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Assembly.lean#L72-L79
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Assembly.lean#L72-L79

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_Assembly
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.conditionalTunnellMap_exactly_two {n : ℤ}
    (odd : BOddRep n ≃ ARep n) (a : ARep n) :
    ∃ x₁ x₂,
      x₁ ≠ x₂ ∧
      conditionalTunnellMap odd x₁ = a ∧
      conditionalTunnellMap odd x₂ = a ∧
      ∀ x, conditionalTunnellMap odd x = a ↔ x = x₁ ∨ x = x₂ := by sorry
