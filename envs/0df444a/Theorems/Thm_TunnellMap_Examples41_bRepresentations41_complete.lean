-- Prove2me | Theorems.Thm_TunnellMap_Examples41_bRepresentations41_complete
-- name    : TunnellMap.Examples41.bRepresentations41_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:51:39.22613+00:00
-- url     : https://prove2.me/theorems/1be5b220-b8e6-4227-8bee-1164b79f4ffa
-- title:
--   Examples41: b Representations41 complete
-- statement:
--   The Examples41 construction uses the b Representations41 complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L136-L140
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L136-L140

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.bRepresentations41_complete (p : Triple) :
    p ∈ bRepresentations41 ↔ bForm p = 41 := by sorry
