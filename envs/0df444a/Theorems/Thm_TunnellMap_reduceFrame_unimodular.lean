-- Prove2me | Theorems.Thm_TunnellMap_reduceFrame_unimodular
-- name    : TunnellMap.reduceFrame_unimodular
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:53:35.380577+00:00
-- url     : https://prove2.me/theorems/c952d3bb-4c1e-4819-965c-8ef92eafe84c
-- title:
--   Tunnell Map: reduce Frame unimodular
-- statement:
--   **The reduction is unimodular** of determinant one.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L325-L329
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L325-L329

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}

theorem TunnellMap.reduceFrame_unimodular (F : OrthogonalFrame p) (hp : p ≠ ⟨0, 0, 0⟩) :
    ∃ a b c d : ℤ, a * d - b * c = 1 ∧
      (reduceFrame F).e₁ = span2 a b F.e₁ F.e₂ ∧
      (reduceFrame F).e₂ = span2 c d F.e₁ F.e₂ := by sorry
