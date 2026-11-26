-- Prove2me | Theorems.Thm_TunnellMap_Examples41_balance_at_41
-- name    : TunnellMap.Examples41.balance_at_41
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:52:22.287125+00:00
-- url     : https://prove2.me/theorems/deca20b6-91e2-40ee-b645-1ecc2f069b76
-- title:
--   Examples41: balance at 41
-- statement:
--   The Examples41 construction uses the balance at 41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L148-L150
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L148-L150

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.balance_at_41 :
    bRepresentations41.card = 2 * aRepresentations41.card := by sorry
