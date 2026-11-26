-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_retained_plus_key_lt
-- name    : TunnellMap.BlockGen.retained_plus_key_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:56.64549+00:00
-- url     : https://prove2.me/theorems/b9b3f82b-a587-4bee-93ff-7e9e900394d5
-- title:
--   Block Gen: retained plus key lt
-- statement:
--   **The retention test is the manuscript's sign condition.**  The target
--   reconstructed at a retained index is the signed representative for which the
--   plus midpoint key is the smaller one.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordSign.lean#L41-L71
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordSign.lean#L41-L71

import Definitions.Def_TunnellMap_BlockGeneratorCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_RecordSign
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {s : BResidual n}

theorem TunnellMap.BlockGen.retained_plus_key_lt (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i : GeneratorIndex} (hret : Retained s F i) {t : AResidual n}
    (ht : residualTargetLift t = targetValue s F i) :
    directionKey (plusVector s t) < directionKey (minusVector s t) := by sorry
