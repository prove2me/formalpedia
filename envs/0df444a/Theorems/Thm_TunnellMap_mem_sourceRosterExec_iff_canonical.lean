-- Prove2me | Theorems.Thm_TunnellMap_mem_sourceRosterExec_iff_canonical
-- name    : TunnellMap.mem_sourceRosterExec_iff_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:18:47.513675+00:00
-- url     : https://prove2.me/theorems/c8f6af68-220c-504b-bb10-fe6838b4aafd
-- title:
--   Tunnell Map: mem source Roster Exec iff canonical
-- statement:
--   The Tunnell Map construction uses the mem source Roster Exec iff canonical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L220-L223
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L220-L223

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_sourceRosterExec_iff_canonical {n : ℤ} (x : BResidual n) :
    x ∈ sourceRosterExec n ↔
      canonicalBResidualRepresentative ((bResidualInvolution n).orbit x) = x := by sorry
