-- Prove2me | Theorems.Thm_TunnellMap_algorithmicResidualOrbitMatching_stable
-- name    : TunnellMap.algorithmicResidualOrbitMatching_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:59:21.262996+00:00
-- url     : https://prove2.me/theorems/1cd35b80-4c9a-55af-82b8-3115c60b4312
-- title:
--   Tunnell Map: algorithmic Residual Orbit Matching stable
-- statement:
--   The Tunnell Map construction uses the algorithmic Residual Orbit Matching stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean#L153-L161
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualDeferredAcceptance.lean#L153-L161

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {n : ℤ} (hnpos : 0 < n)
  [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.algorithmicResidualOrbitMatching_stable
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (residualOrbitRanking hnpos).Stable
      (algorithmicResidualOrbitMatching hnpos hcard) := by sorry
