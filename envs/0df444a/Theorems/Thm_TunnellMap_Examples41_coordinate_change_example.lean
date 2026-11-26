-- Prove2me | Theorems.Thm_TunnellMap_Examples41_coordinate_change_example
-- name    : TunnellMap.Examples41.coordinate_change_example
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:52:36.310521+00:00
-- url     : https://prove2.me/theorems/cbee95d6-1d4e-448b-83cb-398c9aade408
-- title:
--   Examples41: coordinate change example
-- statement:
--   The Examples41 construction uses the coordinate change example property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L160-L165
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L160-L165

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.coordinate_change_example :
    bLift Xcoord = ⟨-4, -1, 2⟩ ∧
      aLift Ycoord = ⟨2, -1, 4⟩ ∧
      qForm (bLift Xcoord) = 41 ∧
      qForm (aLift Ycoord) = 41 := by sorry
