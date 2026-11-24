-- Prove2me | Theorems.Thm_ULHC_adj_other
-- name    : ULHC.adj_other
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:57:21.01438+00:00
-- url     : https://prove2.me/theorems/0120b00b-9b35-4d24-9bb4-eab2d3b9b71f
-- title:
--   ULHC: adj other
-- statement:
--   The ULHC construction uses the adj other property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L404-L411
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L404-L411

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.adj_other {F : Finset Edge} {e : Edge} (he : e ∈ F) {y : Pt} (hy : e.p = y ∨ e.q = y) :
    Adj F y (other e y) := by sorry
