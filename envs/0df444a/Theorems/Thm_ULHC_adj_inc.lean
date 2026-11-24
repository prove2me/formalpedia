-- Prove2me | Theorems.Thm_ULHC_adj_inc
-- name    : ULHC.adj_inc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:46.268339+00:00
-- url     : https://prove2.me/theorems/a12b28f7-6fd6-467e-bba4-bb105707e53d
-- title:
--   ULHC: adj inc
-- statement:
--   The ULHC construction uses the adj inc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L424-L438
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L424-L438

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.adj_inc {F : Finset Edge} {u v : Pt} (h : Adj F u v) :
    ∃ e ∈ F, (e.p = u ∨ e.q = u) ∧ (e.p = v ∨ e.q = v) ∧ v = other e u := by sorry
