-- Prove2me | Theorems.Thm_TunnellMap_residualOrbitMatching_stable
-- name    : TunnellMap.residualOrbitMatching_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:42.882434+00:00
-- url     : https://prove2.me/theorems/24e89d23-eff4-4223-b037-af81c1aa4200
-- title:
--   Tunnell Map: residual Orbit Matching stable
-- statement:
--   The Tunnell Map construction uses the residual Orbit Matching stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrbitRanking.lean#L149-L156
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrbitRanking.lean#L149-L156

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ResidualBalance
import Definitions.Def_TunnellMap_OrbitRanking
set_option autoImplicit true
open TunnellMap
variable {n : ℤ} (hnpos : 0 < n)
  [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.residualOrbitMatching_stable
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (residualOrbitRanking hnpos).Stable
      (residualOrbitMatching hnpos hcard) := by sorry
