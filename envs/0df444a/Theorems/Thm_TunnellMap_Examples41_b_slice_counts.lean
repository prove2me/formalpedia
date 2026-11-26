-- Prove2me | Theorems.Thm_TunnellMap_Examples41_b_slice_counts
-- name    : TunnellMap.Examples41.b_slice_counts
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:49:02.101201+00:00
-- url     : https://prove2.me/theorems/157f053d-a510-5c4c-a75a-d00449f89744
-- title:
--   Examples41: b slice counts
-- statement:
--   The Examples41 construction uses the b slice counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L54-L60
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L54-L60

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.b_slice_counts :
    (bSlice41 0).card = 4 ∧
      (bSlice41 1).card = 8 ∧
      (bSlice41 (-1)).card = 8 ∧
      (bSlice41 2).card = 6 ∧
      (bSlice41 (-2)).card = 6 := by sorry
