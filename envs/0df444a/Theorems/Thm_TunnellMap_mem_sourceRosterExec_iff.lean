-- Prove2me | Theorems.Thm_TunnellMap_mem_sourceRosterExec_iff
-- name    : TunnellMap.mem_sourceRosterExec_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:05:55.139798+00:00
-- url     : https://prove2.me/theorems/d026ba91-4f72-5baa-83e7-d97947306083
-- title:
--   Tunnell Map: mem source Roster Exec iff
-- statement:
--   The Tunnell Map construction uses the mem source Roster Exec iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L175-L178
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L175-L178

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_sourceRosterExec_iff {n : ℤ} (x : BResidual n) :
    x ∈ sourceRosterExec n ↔ IsSourceRosterTriple n x.1.1 := by sorry
