-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_emit_eq_some_iff
-- name    : TunnellMap.BlockGen.emit_eq_some_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:47:46.803725+00:00
-- url     : https://prove2.me/theorems/aa09ca83-9ec0-4c4b-893f-e4f68e07aea7
-- title:
--   Block Gen: emit eq some iff
-- statement:
--   The Block Gen construction uses the emit eq some iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean#L165-L169
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean#L165-L169

import Definitions.Def_TunnellMap_BlockGenerator
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {p : Triple}
variable {s : BResidual n}

theorem TunnellMap.BlockGen.emit_eq_some_iff (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i : GeneratorIndex} {r : IncidentRecord} :
    emit s F i = some r ↔ Retained s F i ∧ r = recordOf s F i := by sorry
