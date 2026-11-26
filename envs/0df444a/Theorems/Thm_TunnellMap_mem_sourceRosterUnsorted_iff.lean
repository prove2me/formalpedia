-- Prove2me | Theorems.Thm_TunnellMap_mem_sourceRosterUnsorted_iff
-- name    : TunnellMap.mem_sourceRosterUnsorted_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:18:00.707705+00:00
-- url     : https://prove2.me/theorems/0767dedb-b3d5-5f30-8eff-193f99264436
-- title:
--   Tunnell Map: mem source Roster Unsorted iff
-- statement:
--   The Tunnell Map construction uses the mem source Roster Unsorted iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L131-L144
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L131-L144

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_sourceRosterUnsorted_iff {n : ℤ} (x : BResidual n) :
    x ∈ sourceRosterUnsorted n ↔ IsSourceRosterTriple n x.1.1 := by sorry
