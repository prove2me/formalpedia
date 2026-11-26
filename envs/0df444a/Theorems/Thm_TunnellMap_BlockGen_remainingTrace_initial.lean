-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_remainingTrace_initial
-- name    : TunnellMap.BlockGen.remainingTrace_initial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:59:28.012197+00:00
-- url     : https://prove2.me/theorems/b91e0c6c-1a4e-4c61-9006-1ef49c255b6d
-- title:
--   Block Gen: remaining Trace initial
-- statement:
--   The Block Gen construction uses the remaining Trace initial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGenerator.lean#L160-L163
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGenerator.lean#L160-L163

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_BlockGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.BlockGen.remainingTrace_initial (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    remainingTrace s F GenState.initial = fullTrace s F := by sorry
