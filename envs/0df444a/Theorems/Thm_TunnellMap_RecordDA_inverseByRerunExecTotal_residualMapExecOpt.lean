-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_inverseByRerunExecTotal_residualMapExecOpt
-- name    : TunnellMap.RecordDA.inverseByRerunExecTotal_residualMapExecOpt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:57:18.658841+00:00
-- url     : https://prove2.me/theorems/0e789b2f-a4a2-4dbf-a3ec-e8ca97e78464
-- title:
--   Record DA: inverse By Rerun Exec Total residual Map Exec Opt
-- statement:
--   First inverse identity for the fallback-free executable inverse.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L214-L223
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L214-L223

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
open TunnellMap.RecordDA
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.inverseByRerunExecTotal_residualMapExecOpt
    (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) :
    inverseByRerunExecTotal hn hnpos hsq hcard
      (canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x) = x := by sorry
