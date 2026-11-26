-- Prove2me | Theorems.Thm_TunnellMap_Examples41_a_slice_counts
-- name    : TunnellMap.Examples41.a_slice_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:49:25.954512+00:00
-- url     : https://prove2.me/theorems/d8c2f6bc-ec12-534b-9115-0141bfb52322
-- title:
--   Examples41: a slice counts
-- statement:
--   The Examples41 construction uses the a slice counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L62-L66
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L62-L66

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.a_slice_counts :
    (aSlice41 0).card = 4 ∧
      (aSlice41 1).card = 6 ∧
      (aSlice41 (-1)).card = 6 := by sorry
