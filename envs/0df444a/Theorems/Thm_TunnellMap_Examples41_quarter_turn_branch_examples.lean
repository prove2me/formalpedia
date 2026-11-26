-- Prove2me | Theorems.Thm_TunnellMap_Examples41_quarter_turn_branch_examples
-- name    : TunnellMap.Examples41.quarter_turn_branch_examples
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:03:51.791003+00:00
-- url     : https://prove2.me/theorems/ac9dc6f9-9f52-53eb-8625-684e5d19893d
-- title:
--   Examples41: quarter turn branch examples
-- statement:
--   The Examples41 construction uses the quarter turn branch examples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L227-L238
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L227-L238

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.quarter_turn_branch_examples :
    (branch1Equiv 11 branch1Source11).rep.1 = ⟨1, -3, 0⟩ ∧
      (branch2Equiv 11 branch2Source11).rep.1 = ⟨1, 3, 0⟩ ∧
      (branch3Equiv 41 branch3Source41).rep.1 = ⟨2, -1, 1⟩ ∧
      (branch3Equiv 41).symm (branch3Equiv 41 branch3Source41) = branch3Source41 := by sorry
