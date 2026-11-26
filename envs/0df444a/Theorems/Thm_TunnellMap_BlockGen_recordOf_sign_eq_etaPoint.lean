-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_recordOf_sign_eq_etaPoint
-- name    : TunnellMap.BlockGen.recordOf_sign_eq_etaPoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:45:09.468198+00:00
-- url     : https://prove2.me/theorems/f41a6e46-f937-44ef-bb96-193ab9bc959c
-- title:
--   Block Gen: record Of sign eq eta Point
-- statement:
--   **The record sign is the canonical edge sign.**  For a retained index whose
--   record stores the canonical lift of the target orbit `o`, the stored sign is
--   `η` of the manuscript, computed from the two canonical representatives.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordSign.lean#L102-L124
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordSign.lean#L102-L124

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_RecordSign
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}

theorem TunnellMap.BlockGen.recordOf_sign_eq_etaPoint (hnpos : 0 < n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) {i : GeneratorIndex}
    (hret : Retained s F i) {o : (aResidualInvolution n hnpos).Orbit}
    (hrt : (recordOf s F i).target = orbitTargetLift hnpos o) :
    (recordOf s F i).sign =
      etaPoint s (canonicalAResidualRepresentative hnpos o) := by sorry
