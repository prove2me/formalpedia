-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_residualMapExec_eq
-- name    : TunnellMap.RecordDA.residualMapExec_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:08:30.829845+00:00
-- url     : https://prove2.me/theorems/32099ea8-0fe1-4e36-b142-c2e9bbae22ac
-- title:
--   Record DA: residual Map Exec eq
-- statement:
--   **Agreement of the executable forward map with the canonical residual
--   map.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L218-L242
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L218-L242

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
variable [Fintype (BOddRep n)] [Fintype (ARep n)]

theorem TunnellMap.RecordDA.residualMapExec_eq (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : AResidual n) (x : BResidual n) :
    residualMapExec hnpos hsq fallback x =
      canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x := by sorry
