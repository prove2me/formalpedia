-- Prove2me | Theorems.Thm_TunnellMap_Examples41_even_branch_example
-- name    : TunnellMap.Examples41.even_branch_example
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:03:23.05417+00:00
-- url     : https://prove2.me/theorems/b595c817-bd2c-4519-aa30-ba19977450a5
-- title:
--   Examples41: even branch example
-- statement:
--   The Examples41 construction uses the even branch example property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L208-L210
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L208-L210

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.even_branch_example :
    (evenEquiv 41 evenSource41).1 = ⟨2, -1, 1⟩ := by sorry
