-- Prove2me | Theorems.Thm_TunnellMap_Examples41_midpoint_bound_attained
-- name    : TunnellMap.Examples41.midpoint_bound_attained
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:54:11.32487+00:00
-- url     : https://prove2.me/theorems/ba72f0c3-e009-404b-b2af-2057229ff861
-- title:
--   Examples41: midpoint bound attained
-- statement:
--   The Examples41 construction uses the midpoint bound attained property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L197-L198
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L197-L198

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.midpoint_bound_attained : qForm ⟨1, -4, 1⟩ = (41 - 1) / 2 := by sorry
