-- Prove2me | Theorems.Thm_TunnellMap_canonical_of_mem_targetRosterExec
-- name    : TunnellMap.canonical_of_mem_targetRosterExec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:15:17.51183+00:00
-- url     : https://prove2.me/theorems/ec9631a3-37e5-56ed-9621-49d4538cde63
-- title:
--   Tunnell Map: canonical of mem target Roster Exec
-- statement:
--   **Soundness.**  Every enumerated point really is a residual target, and it
--   is the canonical representative of its antipodal orbit.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L158-L168
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L158-L168

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.canonical_of_mem_targetRosterExec {n : ℤ} (hnpos : 0 < n)
    {x : AResidual n} (hx : x ∈ targetRosterExec n) :
    canonicalAResidualRepresentative hnpos
      ((aResidualInvolution n hnpos).orbit x) = x := by sorry
