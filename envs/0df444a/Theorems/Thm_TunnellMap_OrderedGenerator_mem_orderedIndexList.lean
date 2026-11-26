-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_mem_orderedIndexList
-- name    : TunnellMap.OrderedGenerator.mem_orderedIndexList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:52:10.10953+00:00
-- url     : https://prove2.me/theorems/693a5d16-618c-4159-b178-478facebfe44
-- title:
--   Ordered Generator: mem ordered Index List
-- statement:
--   The Ordered Generator construction uses the mem ordered Index List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L450-L459
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L450-L459

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.OrderedGenerator.mem_orderedIndexList (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (i : {i // i ∈ validIndices s F}) : i ∈ orderedIndexList s F := by sorry
