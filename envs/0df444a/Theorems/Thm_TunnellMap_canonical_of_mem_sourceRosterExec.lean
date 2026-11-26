-- Prove2me | Theorems.Thm_TunnellMap_canonical_of_mem_sourceRosterExec
-- name    : TunnellMap.canonical_of_mem_sourceRosterExec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:07:02.698+00:00
-- url     : https://prove2.me/theorems/000fd356-1d9f-5e8d-89bc-0b9d6ac0cfc8
-- title:
--   Tunnell Map: canonical of mem source Roster Exec
-- statement:
--   **Soundness.**  Every enumerated point really is a residual source, and it
--   is the canonical representative of its antipodal orbit.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L193-L202
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L193-L202

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.canonical_of_mem_sourceRosterExec {n : ℤ} {x : BResidual n}
    (hx : x ∈ sourceRosterExec n) :
    canonicalBResidualRepresentative ((bResidualInvolution n).orbit x) = x := by sorry
