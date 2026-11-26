-- Prove2me | Theorems.Thm_TunnellMap_algorithmicResidualEquiv_eq
-- name    : TunnellMap.algorithmicResidualEquiv_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:59:00.869711+00:00
-- url     : https://prove2.me/theorems/b0051585-306d-55da-9089-cb1e5d1fac43
-- title:
--   Tunnell Map: algorithmic Residual Equiv eq
-- statement:
--   The executable lift is extensionally the residual equivalence used in the
--   assembled Tunnell map.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean#L205-L212
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean#L205-L212

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {n : ℤ} (hnpos : 0 < n)
  [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.algorithmicResidualEquiv_eq
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    algorithmicResidualEquiv hnpos hcard =
      residualEquivOfOrbitCard hnpos hcard := by sorry
