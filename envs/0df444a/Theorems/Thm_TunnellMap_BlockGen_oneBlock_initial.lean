-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_oneBlock_initial
-- name    : TunnellMap.BlockGen.oneBlock_initial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:37:38.395099+00:00
-- url     : https://prove2.me/theorems/51e4e9f2-98cc-5a90-aca7-5018e1610473
-- title:
--   Block Gen: one Block initial
-- statement:
--   The Block Gen construction uses the one Block initial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorState.lean#L172-L174
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorState.lean#L172-L174

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_BlockGeneratorState
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}

theorem TunnellMap.BlockGen.oneBlock_initial (F : OrthogonalFrame (tau (residualSourceLift s))) :
    OneBlock s F GenState.initial := by sorry
