-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_targetOfValid_key
-- name    : TunnellMap.OrderedGenerator.targetOfValid_key
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:52:25.313106+00:00
-- url     : https://prove2.me/theorems/4ab79d72-56d2-5bb2-aaf2-1c7403316400
-- title:
--   Ordered Generator: target Of Valid key
-- statement:
--   The Ordered Generator construction uses the target Of Valid key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L297-L304
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L297-L304

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.OrderedGenerator.targetOfValid_key (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) :
    directionKey (dValue F i.1) =
      representativeEdgeKey s (targetOfValid s F i) := by sorry
