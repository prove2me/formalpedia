-- Prove2me | Theorems.Thm_TunnellMap_directDomainExec_isSome
-- name    : TunnellMap.directDomainExec_isSome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:25:46.559836+00:00
-- url     : https://prove2.me/theorems/b1fe7488-06d2-498a-86d7-8ef5973ebb8b
-- title:
--   Tunnell Map: direct Domain Exec is Some
-- statement:
--   The Tunnell Map construction uses the direct Domain Exec is Some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirect.lean#L57-L68
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirect.lean#L57-L68

import Definitions.Def_TunnellMap_ResidualBalance
import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableDirect
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.directDomainExec_isSome {n : ℤ} {p : BOddRep n} (h : DirectSourceUsed p) :
    ∃ d : DirectDomain n, directDomainExec p = some d := by sorry
