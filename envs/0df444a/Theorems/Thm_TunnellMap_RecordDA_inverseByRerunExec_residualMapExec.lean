-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_inverseByRerunExec_residualMapExec
-- name    : TunnellMap.RecordDA.inverseByRerunExec_residualMapExec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:21:50.24524+00:00
-- url     : https://prove2.me/theorems/e3008c09-6f01-540b-a283-4c788e5aa1c2
-- title:
--   Record DA: inverse By Rerun Exec residual Map Exec
-- statement:
--   **First inverse identity for the executable pair.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L273-L281
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L273-L281

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

theorem TunnellMap.RecordDA.inverseByRerunExec_residualMapExec (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallbackA : AResidual n) (fallbackB : BResidual n) (x : BResidual n) :
    inverseByRerunExec hsq fallbackB (residualMapExec hnpos hsq fallbackA x) = x := by sorry
