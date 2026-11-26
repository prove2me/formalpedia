-- Prove2me | Theorems.Thm_TunnellMap_directDomainExec_rep
-- name    : TunnellMap.directDomainExec_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:24:51.89683+00:00
-- url     : https://prove2.me/theorems/4738bfa3-e57c-4e61-867d-de605c69ee18
-- title:
--   Tunnell Map: direct Domain Exec rep
-- statement:
--   The Tunnell Map construction uses the direct Domain Exec rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirect.lean#L52-L55
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirect.lean#L52-L55

import Definitions.Def_TunnellMap_ResidualBalance
import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableDirect
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.directDomainExec_rep {n : ℤ} {p : BOddRep n} {d : DirectDomain n}
    (h : directDomainExec p = some d) : directDomainRep d = p := by sorry
