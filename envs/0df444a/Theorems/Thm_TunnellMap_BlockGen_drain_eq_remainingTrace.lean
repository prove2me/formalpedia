-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_drain_eq_remainingTrace
-- name    : TunnellMap.BlockGen.drain_eq_remainingTrace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:38:01.919255+00:00
-- url     : https://prove2.me/theorems/638253b5-1491-48cd-be5f-5f8a2d75cbf4
-- title:
--   Block Gen: drain eq remaining Trace
-- statement:
--   The Block Gen construction uses the drain eq remaining Trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorState.lean#L147-L154
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorState.lean#L147-L154

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_BlockGeneratorState
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}

theorem TunnellMap.BlockGen.drain_eq_remainingTrace (F : OrthogonalFrame (tau (residualSourceLift s)))
    (st : GenState) : drain s F st = remainingTrace s F st := by sorry
