-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_targetOfValid_lift
-- name    : TunnellMap.OrderedGenerator.targetOfValid_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:50:54.687624+00:00
-- url     : https://prove2.me/theorems/3ae38933-e81e-5bf4-9447-7d447076de51
-- title:
--   Ordered Generator: target Of Valid lift
-- statement:
--   The Ordered Generator construction uses the target Of Valid lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L289-L295
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L289-L295

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.OrderedGenerator.targetOfValid_lift (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) :
    residualTargetLift (targetOfValid s F i) = targetValue s F i.1 := by sorry
