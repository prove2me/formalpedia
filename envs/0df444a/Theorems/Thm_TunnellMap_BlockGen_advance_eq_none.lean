-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_advance_eq_none
-- name    : TunnellMap.BlockGen.advance_eq_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:31:41.604942+00:00
-- url     : https://prove2.me/theorems/b2c2521b-2616-5887-89aa-97db9988af4b
-- title:
--   Block Gen: advance eq none
-- statement:
--   The Block Gen construction uses the advance eq none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorState.lean#L121-L124
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorState.lean#L121-L124

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_BlockGeneratorState
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}

theorem TunnellMap.BlockGen.advance_eq_none (F : OrthogonalFrame (tau (residualSourceLift s)))
    {st : GenState} (h : advance s F st = none) :
    remainingTrace s F st = [] := by sorry
