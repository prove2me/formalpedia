-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_orderedIndexList_pairwise
-- name    : TunnellMap.OrderedGenerator.orderedIndexList_pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:51:02.222418+00:00
-- url     : https://prove2.me/theorems/f36a0c63-ab7b-569c-bb0c-0fe0f22bb212
-- title:
--   Ordered Generator: ordered Index List pairwise
-- statement:
--   The Ordered Generator construction uses the ordered Index List pairwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L433-L440
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L433-L440

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.OrderedGenerator.orderedIndexList_pairwise (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (orderedIndexList s F).Pairwise fun i j =>
      directionKey (dValue F i.1) ≤ directionKey (dValue F j.1) := by sorry
