-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_residualMapExec_inverseByRerunExec
-- name    : TunnellMap.RecordDA.residualMapExec_inverseByRerunExec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:21:55.843797+00:00
-- url     : https://prove2.me/theorems/88b3729d-21d8-432e-b40b-11c304fb6cf6
-- title:
--   Record DA: residual Map Exec inverse By Rerun Exec
-- statement:
--   **Second inverse identity for the executable pair.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L284-L292
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L284-L292

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_InverseByRerun
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ComputablePipeline
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
variable [Fintype (BOddRep n)]
variable [Fintype (ARep n)]

theorem TunnellMap.RecordDA.residualMapExec_inverseByRerunExec (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallbackA : AResidual n) (fallbackB : BResidual n) (y : AResidual n) :
    residualMapExec hnpos hsq fallbackA (inverseByRerunExec hsq fallbackB y) = y := by sorry
