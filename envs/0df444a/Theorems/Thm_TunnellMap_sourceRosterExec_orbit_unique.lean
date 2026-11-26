-- Prove2me | Theorems.Thm_TunnellMap_sourceRosterExec_orbit_unique
-- name    : TunnellMap.sourceRosterExec_orbit_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:20:14.3724+00:00
-- url     : https://prove2.me/theorems/2c71ca55-040d-4d5f-8570-f743c612960f
-- title:
--   Tunnell Map: source Roster Exec orbit unique
-- statement:
--   **Every residual source orbit occurs exactly once.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L226-L235
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L226-L235

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.sourceRosterExec_orbit_unique {n : ℤ}
    (q : (bResidualInvolution n).Orbit) :
    ∃! x : BResidual n, x ∈ sourceRosterExec n ∧
      (bResidualInvolution n).orbit x = q := by sorry
