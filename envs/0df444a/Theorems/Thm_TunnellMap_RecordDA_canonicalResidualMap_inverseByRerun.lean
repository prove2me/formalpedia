-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_canonicalResidualMap_inverseByRerun
-- name    : TunnellMap.RecordDA.canonicalResidualMap_inverseByRerun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:06:12.146296+00:00
-- url     : https://prove2.me/theorems/34bd37d0-1dd4-4aa3-a6a1-5563329826d4
-- title:
--   Record DA: canonical Residual Map inverse By Rerun
-- statement:
--   **Second inverse identity.**  The canonical residual map sends the point
--   recovered by rerunning back to the given residual target point.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L275-L298
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L275-L298

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

theorem TunnellMap.RecordDA.canonicalResidualMap_inverseByRerun (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : BResidual n) (y : AResidual n) :
    canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard)
        (inverseByRerun frames fallback y) = y := by sorry
