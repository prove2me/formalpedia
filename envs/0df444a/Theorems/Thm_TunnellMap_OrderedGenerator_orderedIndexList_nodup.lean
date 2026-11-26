-- Prove2me | Theorems.Thm_TunnellMap_OrderedGenerator_orderedIndexList_nodup
-- name    : TunnellMap.OrderedGenerator.orderedIndexList_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:50:33.35222+00:00
-- url     : https://prove2.me/theorems/c4c16b23-eb53-581c-ab65-d9cd2b79423d
-- title:
--   Ordered Generator: ordered Index List nodup
-- statement:
--   The Ordered Generator construction uses the ordered Index List nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L442-L448
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrderedGenerator.lean#L442-L448

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}

theorem TunnellMap.OrderedGenerator.orderedIndexList_nodup (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (orderedIndexList s F).Nodup := by sorry
