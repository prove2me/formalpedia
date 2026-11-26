-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_residualMapExecTotal_inverseByRerunExecTotal
-- name    : TunnellMap.RecordDA.residualMapExecTotal_inverseByRerunExecTotal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:56:57.678144+00:00
-- url     : https://prove2.me/theorems/4cff3582-2260-5dfb-83f7-25d614fc859b
-- title:
--   Record DA: residual Map Exec Total inverse By Rerun Exec Total
-- statement:
--   Second inverse identity for the two public fallback-free residual
--   interfaces.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L251-L259
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L251-L259

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
open TunnellMap.RecordDA
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.residualMapExecTotal_inverseByRerunExecTotal
    (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (y : AResidual n) :
    residualMapExecTotal hn hnpos hsq hcard
      (inverseByRerunExecTotal hn hnpos hsq hcard y) = y := by sorry
