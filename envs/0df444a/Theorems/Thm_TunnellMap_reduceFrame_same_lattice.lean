-- Prove2me | Theorems.Thm_TunnellMap_reduceFrame_same_lattice
-- name    : TunnellMap.reduceFrame_same_lattice
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:52:47.2438+00:00
-- url     : https://prove2.me/theorems/516928ce-4892-5ff8-bb7a-0d8b4a43d36e
-- title:
--   Tunnell Map: reduce Frame same lattice
-- statement:
--   **The reduction spans the same lattice.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L332-L335
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L332-L335

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}

theorem TunnellMap.reduceFrame_same_lattice (F : OrthogonalFrame p) (r : Triple) :
    (∃ a b : ℤ, r = span2 a b F.e₁ F.e₂) ↔
      (∃ a b : ℤ, r = span2 a b (reduceFrame F).e₁ (reduceFrame F).e₂) := by sorry
