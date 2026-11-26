-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_orderedIndexList_key_strict
-- name    : TunnellMap.OrderedGenerator.orderedIndexList_key_strict
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:54:12.59256+00:00
-- url     : https://prove2.me/theorems/8178eb1d-179c-4e7b-8b8d-72eb29294929
-- title:
--   Ordered Generator: ordered Index List key strict
-- statement:
--   The Ordered Generator construction uses the ordered Index List key strict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L461-L472
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L461-L472

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.OrderedGenerator.orderedIndexList_key_strict (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    {i j : Fin (orderedIndexList s F).length} (hij : i < j) :
    directionKey (dValue F ((orderedIndexList s F).get i).1) <
      directionKey (dValue F ((orderedIndexList s F).get j).1) := by sorry
