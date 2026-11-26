-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_drain_initial
-- name    : TunnellMap.BlockGen.drain_initial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:10.429288+00:00
-- url     : https://prove2.me/theorems/9959c970-5098-47c5-b6a1-cb5b0d3a0653
-- title:
--   Block Gen: drain initial
-- statement:
--   **Termination and total correctness of the executable run.**  Draining the
--   generator from its initial state produces exactly the complete trace.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorState.lean#L158-L160
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorState.lean#L158-L160

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_BlockGeneratorState
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}

theorem TunnellMap.BlockGen.drain_initial (F : OrthogonalFrame (tau (residualSourceLift s))) :
    drain s F GenState.initial = fullTrace s F := by sorry
