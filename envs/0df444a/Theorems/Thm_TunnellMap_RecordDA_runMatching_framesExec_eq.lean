-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_runMatching_framesExec_eq
-- name    : TunnellMap.RecordDA.runMatching_framesExec_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:37:19.550681+00:00
-- url     : https://prove2.me/theorems/cd1429f7-1c4a-56db-b1ad-6668fd5a5484
-- title:
--   Record DA: run Matching frames Exec eq
-- statement:
--   **The executable run computes the structural stable matching.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L117-L123
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L117-L123

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

theorem TunnellMap.RecordDA.runMatching_framesExec_eq (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    runMatching hn hnpos (framesExec hsq) hcard =
      residualOrbitMatching hnpos hcard := by sorry
