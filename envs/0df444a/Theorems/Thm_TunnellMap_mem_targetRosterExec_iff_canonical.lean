-- Prove2me | Theorems.Thm_TunnellMap_mem_targetRosterExec_iff_canonical
-- name    : TunnellMap.mem_targetRosterExec_iff_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:41:17.908096+00:00
-- url     : https://prove2.me/theorems/e6fd7272-b779-5c20-abe4-332896869eb7
-- title:
--   Tunnell Map: mem target Roster Exec iff canonical
-- statement:
--   The Tunnell Map construction uses the mem target Roster Exec iff canonical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L190-L195
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L190-L195

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_targetRosterExec_iff_canonical {n : ℤ} (hnpos : 0 < n)
    (x : AResidual n) :
    x ∈ targetRosterExec n ↔
      canonicalAResidualRepresentative hnpos
        ((aResidualInvolution n hnpos).orbit x) = x := by sorry
