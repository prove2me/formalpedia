-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_residualMapExecOpt_inverseByRerunExecTotal
-- name    : TunnellMap.RecordDA.residualMapExecOpt_inverseByRerunExecTotal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:56:03.730907+00:00
-- url     : https://prove2.me/theorems/5b948c0c-9f0c-518f-8708-31acfd1c1735
-- title:
--   Record DA: residual Map Exec Opt inverse By Rerun Exec Total
-- statement:
--   Second inverse identity for the fallback-free executable inverse.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L226-L235
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L226-L235

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
open TunnellMap.RecordDA
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.residualMapExecOpt_inverseByRerunExecTotal
    (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (y : AResidual n) :
    canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard)
      (inverseByRerunExecTotal hn hnpos hsq hcard y) = y := by sorry
