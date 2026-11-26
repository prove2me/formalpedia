-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_advance_nil_of_gt
-- name    : TunnellMap.BlockGen.advance_nil_of_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:48:33.964236+00:00
-- url     : https://prove2.me/theorems/6f49aed5-36a0-57b0-a3d2-81078b9d5dc6
-- title:
--   Block Gen: advance nil of gt
-- statement:
--   The generator stops exactly when the outer loop is finished.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorState.lean#L103-L105
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorState.lean#L103-L105

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_BlockGeneratorState
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}

theorem TunnellMap.BlockGen.advance_nil_of_gt (F : OrthogonalFrame (tau (residualSourceLift s)))
    {h : ℤ} (hgt : ¬ h ≤ hMax n) : advance s F ⟨h, []⟩ = none := by sorry
