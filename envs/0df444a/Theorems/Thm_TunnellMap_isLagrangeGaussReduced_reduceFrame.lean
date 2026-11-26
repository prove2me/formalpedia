-- Prove2me | Theorems.Thm_TunnellMap_isLagrangeGaussReduced_reduceFrame
-- name    : TunnellMap.isLagrangeGaussReduced_reduceFrame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:56:18.150946+00:00
-- url     : https://prove2.me/theorems/f58476d5-4846-525f-af0d-9ed45f8084e8
-- title:
--   Tunnell Map: is Lagrange Gauss Reduced reduce Frame
-- statement:
--   **The computed frame satisfies the manuscript's reducedness
--   predicate.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L310-L312
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/LagrangeGauss.lean#L310-L312

import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ReducedBasisBound
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_LagrangeGauss
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {p : Triple}

theorem TunnellMap.isLagrangeGaussReduced_reduceFrame (F : OrthogonalFrame p) :
    IsLagrangeGaussReduced (reduceFrame F) := by sorry
