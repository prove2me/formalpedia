-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_residualMapExecTotal_eq_canonical
-- name    : TunnellMap.RecordDA.residualMapExecTotal_eq_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:57:10.040596+00:00
-- url     : https://prove2.me/theorems/cbe1d9be-5203-46a2-9880-5f8b0a183223
-- title:
--   Record DA: residual Map Exec Total eq canonical
-- statement:
--   The fallback-free executable residual map agrees with the structural
--   residual correspondence.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L113-L124
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L113-L124

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
open TunnellMap.RecordDA
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.residualMapExecTotal_eq_canonical (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) :
    residualMapExecTotal hn hnpos hsq hcard x =
      canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x := by sorry
