-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_inverseByRerunExec_eq_residualEquiv_symm
-- name    : TunnellMap.RecordDA.inverseByRerunExec_eq_residualEquiv_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:21:54.578062+00:00
-- url     : https://prove2.me/theorems/6a866b76-c019-57ba-ad92-b22733ab603d
-- title:
--   Record DA: inverse By Rerun Exec eq residual Equiv symm
-- statement:
--   The executable inverse agrees with the inverse of the structural
--   equivalence.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L309-L318
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L309-L318

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

theorem TunnellMap.RecordDA.inverseByRerunExec_eq_residualEquiv_symm (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : BResidual n) (y : AResidual n) :
    inverseByRerunExec hsq fallback y =
      (residualEquivOfOrbitCard hnpos hcard).symm y := by sorry
