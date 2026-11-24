-- Prove2me | Theorems.Thm_ULHC_adj_iff_inc
-- name    : ULHC.adj_iff_inc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:31.325464+00:00
-- url     : https://prove2.me/theorems/be35cf9d-c737-49f3-994c-83aff5f99f7d
-- title:
--   ULHC: adj iff inc
-- statement:
--   The ULHC construction uses the adj iff inc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L247-L248
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L247-L248

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.adj_iff_inc {F : Finset Edge} {x y : Pt} :
    Adj F x y ↔ ∃ e ∈ F, (e.p = x ∧ e.q = y) ∨ (e.p = y ∧ e.q = x) := by sorry
