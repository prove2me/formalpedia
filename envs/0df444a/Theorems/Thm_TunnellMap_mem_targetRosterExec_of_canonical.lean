-- Prove2me | Theorems.Thm_TunnellMap_mem_targetRosterExec_of_canonical
-- name    : TunnellMap.mem_targetRosterExec_of_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:15:10.589942+00:00
-- url     : https://prove2.me/theorems/5513df9a-2442-50bc-bdc7-62adc8f1f487
-- title:
--   Tunnell Map: mem target Roster Exec of canonical
-- statement:
--   **Completeness.**  The canonical representative of every residual target
--   orbit is enumerated.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L172-L188
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L172-L188

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_targetRosterExec_of_canonical {n : ℤ} (hnpos : 0 < n)
    {x : AResidual n}
    (hx : canonicalAResidualRepresentative hnpos
      ((aResidualInvolution n hnpos).orbit x) = x) :
    x ∈ targetRosterExec n := by sorry
