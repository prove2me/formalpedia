-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_inverseByRerunExecTotal_residualMapExecTotal
-- name    : TunnellMap.RecordDA.inverseByRerunExecTotal_residualMapExecTotal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:56:40.584412+00:00
-- url     : https://prove2.me/theorems/56fe056a-33af-5c86-9368-0c20f831cd15
-- title:
--   Record DA: inverse By Rerun Exec Total residual Map Exec Total
-- statement:
--   First inverse identity for the two public fallback-free residual
--   interfaces.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L239-L247
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L239-L247

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
open TunnellMap.RecordDA
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.inverseByRerunExecTotal_residualMapExecTotal
    (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) :
    inverseByRerunExecTotal hn hnpos hsq hcard
      (residualMapExecTotal hn hnpos hsq hcard x) = x := by sorry
