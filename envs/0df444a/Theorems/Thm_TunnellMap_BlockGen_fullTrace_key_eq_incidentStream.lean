-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_fullTrace_key_eq_incidentStream
-- name    : TunnellMap.BlockGen.fullTrace_key_eq_incidentStream
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:31:43.387806+00:00
-- url     : https://prove2.me/theorems/404f1209-a681-4f5d-ba73-b03f3da27370
-- title:
--   Block Gen: full Trace key eq incident Stream
-- statement:
--   The emitted keys are exactly the orbit edge keys of the incident stream.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean#L499-L507
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean#L499-L507

import Definitions.Def_TunnellMap_BlockGenerator
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {p : Triple}
variable {s : BResidual n}

theorem TunnellMap.BlockGen.fullTrace_key_eq_incidentStream (hnpos : 0 < n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (fullTrace s F).map IncidentRecord.key =
      (incidentStream hnpos s F).map
        (orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)) := by sorry
