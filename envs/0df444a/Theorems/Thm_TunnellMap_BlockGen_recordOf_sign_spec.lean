-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_recordOf_sign_spec
-- name    : TunnellMap.BlockGen.recordOf_sign_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:01.011139+00:00
-- url     : https://prove2.me/theorems/824c1d0c-e241-5b11-9fe8-99bc6d16e6dd
-- title:
--   Block Gen: record Of sign spec
-- statement:
--   The record's sign recovers the manuscript's signed reconstructed target
--   from the canonical orbit representative stored in the record.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean#L444-L447
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean#L444-L447

import Definitions.Def_TunnellMap_BlockGenerator
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {p : Triple}
variable {s : BResidual n}

theorem TunnellMap.BlockGen.recordOf_sign_spec (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : GeneratorIndex) :
    targetValue s F i = vsmul (recordOf s F i).sign (recordOf s F i).target := by sorry
