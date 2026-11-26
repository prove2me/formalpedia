-- Prove2me | Theorems.Thm_TunnellMap_Examples41_pure_coordinate_change_example
-- name    : TunnellMap.Examples41.pure_coordinate_change_example
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:53:48.71561+00:00
-- url     : https://prove2.me/theorems/02d8ef51-12ea-4c43-b1a0-803a39c44c2e
-- title:
--   Examples41: pure coordinate change example
-- statement:
--   The Examples41 construction uses the pure coordinate change example property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L167-L176
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L167-L176

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.pure_coordinate_change_example :
    (eBEquiv 41 Xcoord).1 = ⟨-2, -6, -1⟩ ∧
      (eAEquiv 41 Ycoord).1 = ⟨6, -2, -1⟩ ∧
      (eBEquiv 41).symm (eBEquiv 41 Xcoord) = Xcoord ∧
      (eAEquiv 41).symm (eAEquiv 41 Ycoord) = Ycoord := by sorry
