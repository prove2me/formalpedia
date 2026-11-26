-- Prove2me | Theorems.Thm_TunnellMap_directTargetUnionEquiv_val
-- name    : TunnellMap.directTargetUnionEquiv_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:25:15.901016+00:00
-- url     : https://prove2.me/theorems/c6ac0781-c51e-576f-a929-96e0f5b70898
-- title:
--   Tunnell Map: direct Target Union Equiv val
-- statement:
--   The Tunnell Map construction uses the direct Target Union Equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirect.lean#L76-L78
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirect.lean#L76-L78

import Definitions.Def_TunnellMap_ResidualBalance
import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableDirect
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.directTargetUnionEquiv_val {n : ℤ} (hn : Odd n) (i : DirectImage n) :
    (directTargetUnionEquiv hn i).1 = directImageRep i := by sorry
