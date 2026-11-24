-- Prove2me | Theorems.Thm_ULHC_adj_insert
-- name    : ULHC.adj_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:52.176159+00:00
-- url     : https://prove2.me/theorems/84beacff-980c-4c36-9112-8ebc9edcd67f
-- title:
--   ULHC: adj insert
-- statement:
--   The ULHC construction uses the adj insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L30-L42
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L30-L42

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.adj_insert {F : Finset Edge} {e : Edge} {a b : Pt} :
    Adj (insert e F) a b ↔ Adj F a b ∨ (a = e.p ∧ b = e.q) ∨ (a = e.q ∧ b = e.p) := by sorry
