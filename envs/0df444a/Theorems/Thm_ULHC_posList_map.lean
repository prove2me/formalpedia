-- Prove2me | Theorems.Thm_ULHC_posList_map
-- name    : ULHC.posList_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:58:06.922506+00:00
-- url     : https://prove2.me/theorems/e9751388-e3f5-42e4-842c-b6c85e246c7d
-- title:
--   ULHC: pos List map
-- statement:
--   The ULHC construction uses the pos List map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L114-L116
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L114-L116

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.posList_map : ∀ (L : List StripSpec) (k : ℕ), (posList k L).map Node.σ = L
  := by sorry
