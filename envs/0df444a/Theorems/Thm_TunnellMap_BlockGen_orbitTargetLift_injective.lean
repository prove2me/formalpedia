-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_orbitTargetLift_injective
-- name    : TunnellMap.BlockGen.orbitTargetLift_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:30:20.186872+00:00
-- url     : https://prove2.me/theorems/e068ed6f-9ffd-4032-a4fb-d982e1c9415a
-- title:
--   Block Gen: orbit Target Lift injective
-- statement:
--   The Block Gen construction uses the orbit Target Lift injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean#L420-L432
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean#L420-L432

import Definitions.Def_TunnellMap_BlockGenerator
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {p : Triple}
variable {s : BResidual n}

theorem TunnellMap.BlockGen.orbitTargetLift_injective {n : ℤ} (hnpos : 0 < n) :
    Function.Injective (orbitTargetLift hnpos) := by sorry
