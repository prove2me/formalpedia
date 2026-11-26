-- Prove2me | Theorems.Thm_TunnellMap_directSourceUnionEquiv_val
-- name    : TunnellMap.directSourceUnionEquiv_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:24:56.366947+00:00
-- url     : https://prove2.me/theorems/f5658cc0-940c-5ae0-932a-eb50f125a619
-- title:
--   Tunnell Map: direct Source Union Equiv val
-- statement:
--   The Tunnell Map construction uses the direct Source Union Equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirect.lean#L72-L74
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirect.lean#L72-L74

import Definitions.Def_TunnellMap_ResidualBalance
import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableDirect
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.directSourceUnionEquiv_val {n : ℤ} (hn : Odd n) (d : DirectDomain n) :
    (directSourceUnionEquiv hn d).1 = directDomainRep d := by sorry
