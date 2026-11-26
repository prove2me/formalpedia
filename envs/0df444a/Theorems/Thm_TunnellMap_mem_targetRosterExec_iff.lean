-- Prove2me | Theorems.Thm_TunnellMap_mem_targetRosterExec_iff
-- name    : TunnellMap.mem_targetRosterExec_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:16:19.37228+00:00
-- url     : https://prove2.me/theorems/8fcbe9ae-2609-4d60-afec-d25bd2af51f4
-- title:
--   Tunnell Map: mem target Roster Exec iff
-- statement:
--   The Tunnell Map construction uses the mem target Roster Exec iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L140-L143
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L140-L143

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_targetRosterExec_iff {n : ℤ} (x : AResidual n) :
    x ∈ targetRosterExec n ↔ IsTargetRosterTriple n x.1.1 := by sorry
