-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_inverseByRerunExecTotal_eq_residualEquiv_symm
-- name    : TunnellMap.RecordDA.inverseByRerunExecTotal_eq_residualEquiv_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:56:02.494248+00:00
-- url     : https://prove2.me/theorems/90eb53be-dd1d-4764-b7c2-11e611bb0611
-- title:
--   Record DA: inverse By Rerun Exec Total eq residual Equiv symm
-- statement:
--   The fallback-free executable inverse agrees with the inverse of the
--   structural residual equivalence.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L195-L211
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/FallbackFreeMap.lean#L195-L211

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
open TunnellMap.RecordDA
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.inverseByRerunExecTotal_eq_residualEquiv_symm
    (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (y : AResidual n) :
    inverseByRerunExecTotal hn hnpos hsq hcard y =
      (residualEquivOfOrbitCard hnpos hcard).symm y := by sorry
