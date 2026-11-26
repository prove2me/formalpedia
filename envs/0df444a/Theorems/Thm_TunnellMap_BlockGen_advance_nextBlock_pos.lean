-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_advance_nextBlock_pos
-- name    : TunnellMap.BlockGen.advance_nextBlock_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:21:52.017166+00:00
-- url     : https://prove2.me/theorems/bbdbf4d0-cb78-5e95-a16a-13e60adecc8e
-- title:
--   Block Gen: advance next Block pos
-- statement:
--   The generator never moves its block cursor below its starting value.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelPipeline.lean#L30-L66
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelPipeline.lean#L30-L66

import Definitions.Def_TunnellMap_KernelGenerator
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_KernelPipeline
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
variable {n : ℤ} {s : BResidual n}

theorem TunnellMap.BlockGen.advance_nextBlock_pos (F : OrthogonalFrame (tau (residualSourceLift s)))
    {st : GenState} (hst : 1 ≤ st.nextBlock) {r : IncidentRecord} {st' : GenState}
    (h : advance s F st = some (r, st')) : 1 ≤ st'.nextBlock := by sorry
