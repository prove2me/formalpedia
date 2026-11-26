-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_residualMapExec_eq_residualEquiv
-- name    : TunnellMap.RecordDA.residualMapExec_eq_residualEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:21:57.90235+00:00
-- url     : https://prove2.me/theorems/fc5d1e8f-91f2-53e4-a082-7109b7bafcf2
-- title:
--   Record DA: residual Map Exec eq residual Equiv
-- statement:
--   The executable forward map agrees with the structural residual
--   equivalence.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L322-L330
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L322-L330

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

theorem TunnellMap.RecordDA.residualMapExec_eq_residualEquiv (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : AResidual n) (x : BResidual n) :
    residualMapExec hnpos hsq fallback x =
      residualEquivOfOrbitCard hnpos hcard x := by sorry
