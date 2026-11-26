-- Prove2me | Theorems.Thm_TunnellMap_residualOrbitMatching_unique
-- name    : TunnellMap.residualOrbitMatching_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:43:53.074856+00:00
-- url     : https://prove2.me/theorems/f0d29776-39f0-5075-9f0a-9aaf0ae3fd42
-- title:
--   Tunnell Map: residual Orbit Matching unique
-- statement:
--   The Tunnell Map construction uses the residual Orbit Matching unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrbitRanking.lean#L158-L167
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrbitRanking.lean#L158-L167

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ResidualBalance
import Definitions.Def_TunnellMap_OrbitRanking
set_option autoImplicit true
open TunnellMap
variable {n : ℤ} (hnpos : 0 < n)
  [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.residualOrbitMatching_unique
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (M : (bResidualInvolution n).Orbit ≃
      (aResidualInvolution n hnpos).Orbit)
    (hM : (residualOrbitRanking hnpos).Stable M) :
    M = residualOrbitMatching hnpos hcard := by sorry
