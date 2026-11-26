-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_inverseByRerun_canonicalResidualMap
-- name    : TunnellMap.RecordDA.inverseByRerun_canonicalResidualMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:09:41.508144+00:00
-- url     : https://prove2.me/theorems/2f907f30-28b9-4e19-a76d-2982b7a215dc
-- title:
--   Record DA: inverse By Rerun canonical Residual Map
-- statement:
--   **First inverse identity.**  Rerunning the computation at the image of a
--   residual source point returns that point, signs included.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L240-L271
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L240-L271

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)]
variable [Fintype (ARep n)]

theorem TunnellMap.RecordDA.inverseByRerun_canonicalResidualMap (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : BResidual n) (x : BResidual n) :
    inverseByRerun frames fallback
        (canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x) = x := by sorry
