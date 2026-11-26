-- Prove2me | Theorems.Thm_TunnellMap_Examples41_box41_complete_for_a
-- name    : TunnellMap.Examples41.box41_complete_for_a
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:17:09.843434+00:00
-- url     : https://prove2.me/theorems/aec48a13-4994-5ee3-a6a3-6803998cddd5
-- title:
--   Examples41: box41 complete for a
-- statement:
--   The Examples41 construction uses the box41 complete for a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L105-L134
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L105-L134

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.box41_complete_for_a (p : Triple) (hp : aForm p = 41) : p ∈ box41 := by sorry
