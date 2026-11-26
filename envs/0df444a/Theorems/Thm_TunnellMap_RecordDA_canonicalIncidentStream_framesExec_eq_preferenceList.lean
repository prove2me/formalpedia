-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_canonicalIncidentStream_framesExec_eq_preferenceList
-- name    : TunnellMap.RecordDA.canonicalIncidentStream_framesExec_eq_preferenceList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:36:50.236044+00:00
-- url     : https://prove2.me/theorems/9b5a0074-de87-543d-9f75-73f03cdf308a
-- title:
--   Record DA: canonical Incident Stream frames Exec eq preference List
-- statement:
--   **The computed frame generates the manuscript's preference row.**  This is
--   the hypothesis `BlockGen` and `RecordDA` require of a frame family: the
--   incident stream produced from it is the globally ranked preference list of the
--   source orbit.  It replaces the `Classical.choice` frame of
--   `canonicalIncidentStream_eq_preferenceList`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L83-L93
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L83-L93

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

theorem TunnellMap.RecordDA.canonicalIncidentStream_framesExec_eq_preferenceList
    (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (q : (bResidualInvolution n).Orbit) :
    incidentStream hnpos (canonicalBResidualRepresentative q)
        (framesExec hsq (canonicalBResidualRepresentative q)) =
      (residualOrbitRanking hnpos).preferenceList q := by sorry
