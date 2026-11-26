-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_residualMapExec_bijective
-- name    : TunnellMap.RecordDA.residualMapExec_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:37:49.81681+00:00
-- url     : https://prove2.me/theorems/38680305-aaa6-4734-a993-18789e2906b4
-- title:
--   Record DA: residual Map Exec bijective
-- statement:
--   **The executable residual map is a bijection**, with the executable
--   rerun inverse as its two-sided inverse.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L296-L305
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L296-L305

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

theorem TunnellMap.RecordDA.residualMapExec_bijective (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallbackA : AResidual n) (fallbackB : BResidual n) :
    Function.Bijective (residualMapExec hnpos hsq fallbackA) := by sorry
