-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_advance_cons
-- name    : TunnellMap.BlockGen.advance_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:48:28.630632+00:00
-- url     : https://prove2.me/theorems/5489cdc9-b81c-4129-be3c-d4b95ed2a2d6
-- title:
--   Block Gen: advance cons
-- statement:
--   Emission step: while the stored block still has records, the first one is
--   emitted and the block index does not move.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorState.lean#L91-L94
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorState.lean#L91-L94

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_BlockGeneratorState
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}

theorem TunnellMap.BlockGen.advance_cons (F : OrthogonalFrame (tau (residualSourceLift s))) (h : ℤ)
    (r : IncidentRecord) (rest : List IncidentRecord) :
    advance s F ⟨h, r :: rest⟩ = some (r, ⟨h, rest⟩) := by sorry
