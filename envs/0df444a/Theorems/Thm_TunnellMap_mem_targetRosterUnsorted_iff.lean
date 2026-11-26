-- Prove2me | Theorems.Thm_TunnellMap_mem_targetRosterUnsorted_iff
-- name    : TunnellMap.mem_targetRosterUnsorted_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:26:58.712691+00:00
-- url     : https://prove2.me/theorems/370d93d5-89c7-4b8d-b4c3-74fa30dca6bf
-- title:
--   Tunnell Map: mem target Roster Unsorted iff
-- statement:
--   The Tunnell Map construction uses the mem target Roster Unsorted iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L96-L109
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L96-L109

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_targetRosterUnsorted_iff {n : ℤ} (x : AResidual n) :
    x ∈ targetRosterUnsorted n ↔ IsTargetRosterTriple n x.1.1 := by sorry
