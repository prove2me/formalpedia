-- Prove2me | Theorems.Thm_TunnellMap_targetRosterExec_orbit_unique
-- name    : TunnellMap.targetRosterExec_orbit_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:27:13.636653+00:00
-- url     : https://prove2.me/theorems/7c94c802-7c5c-5c3f-83ea-551e942ec527
-- title:
--   Tunnell Map: target Roster Exec orbit unique
-- statement:
--   **Every residual target orbit occurs exactly once.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L198-L207
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L198-L207

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.targetRosterExec_orbit_unique {n : ℤ} (hnpos : 0 < n)
    (q : (aResidualInvolution n hnpos).Orbit) :
    ∃! x : AResidual n, x ∈ targetRosterExec n ∧
      (aResidualInvolution n hnpos).orbit x = q := by sorry
