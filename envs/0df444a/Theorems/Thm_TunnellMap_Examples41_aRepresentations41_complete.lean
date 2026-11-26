-- Prove2me | Theorems.Thm_TunnellMap_Examples41_aRepresentations41_complete
-- name    : TunnellMap.Examples41.aRepresentations41_complete
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:52:08.382011+00:00
-- url     : https://prove2.me/theorems/fb9ef8bd-0a7b-41ec-85b3-8f26031b242d
-- title:
--   Examples41: a Representations41 complete
-- statement:
--   The Examples41 construction uses the a Representations41 complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L142-L146
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L142-L146

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.aRepresentations41_complete (p : Triple) :
    p ∈ aRepresentations41 ↔ aForm p = 41 := by sorry
