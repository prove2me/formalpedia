-- Prove2me | Theorems.Thm_ULHC_posList_mem
-- name    : ULHC.posList_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:58:16.501804+00:00
-- url     : https://prove2.me/theorems/51885d4a-e081-4e54-8a90-143e101cbe89
-- title:
--   ULHC: pos List mem
-- statement:
--   The ULHC construction uses the pos List mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L125-L133
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/LinkGraph.lean#L125-L133

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_LinkGraph
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.posList_mem : ∀ (L : List StripSpec) (k : ℕ), k ≤ 3 → ∀ x ∈ posList k L,
    x.σ ∈ L ∧ k ≤ x.pos ∧ x.pos ≤ 3
  := by sorry
