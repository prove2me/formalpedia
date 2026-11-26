-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_canonicalResidualMap_bijective
-- name    : TunnellMap.RecordDA.canonicalResidualMap_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:35:33.756367+00:00
-- url     : https://prove2.me/theorems/3d4ace68-7c8f-4743-86a7-fca970666a4e
-- title:
--   Record DA: canonical Residual Map bijective
-- statement:
--   The canonical residual map is a bijection with `inverseByRerun` as its
--   two-sided inverse.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L317-L327
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/InverseByRerun.lean#L317-L327

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

theorem TunnellMap.RecordDA.canonicalResidualMap_bijective (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : BResidual n) :
    Function.Bijective
      (canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard)) := by sorry
