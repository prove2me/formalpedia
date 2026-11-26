-- Prove2me | Theorems.Thm_TunnellMap_mem_sourceRosterExec_of_canonical
-- name    : TunnellMap.mem_sourceRosterExec_of_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:07:58.135426+00:00
-- url     : https://prove2.me/theorems/ea8622b9-166e-439a-bd35-c4a22ce0e316
-- title:
--   Tunnell Map: mem source Roster Exec of canonical
-- statement:
--   **Completeness.**  The canonical representative of every residual source
--   orbit is enumerated.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L206-L218
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L206-L218

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_sourceRosterExec_of_canonical {n : ℤ} {x : BResidual n}
    (hx : canonicalBResidualRepresentative ((bResidualInvolution n).orbit x) = x) :
    x ∈ sourceRosterExec n := by sorry
