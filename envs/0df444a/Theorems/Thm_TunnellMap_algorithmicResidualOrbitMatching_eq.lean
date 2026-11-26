-- Prove2me | Theorems.Thm_TunnellMap_algorithmicResidualOrbitMatching_eq
-- name    : TunnellMap.algorithmicResidualOrbitMatching_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:00:01.547082+00:00
-- url     : https://prove2.me/theorems/56f54925-907a-554c-bce1-8428f43320b2
-- title:
--   Tunnell Map: algorithmic Residual Orbit Matching eq
-- statement:
--   The executable FIFO construction agrees with the abstract matching used
--   elsewhere in the paper.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean#L165-L172
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean#L165-L172

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {n : ℤ} (hnpos : 0 < n)
  [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.algorithmicResidualOrbitMatching_eq
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    algorithmicResidualOrbitMatching hnpos hcard =
      residualOrbitMatching hnpos hcard := by sorry
