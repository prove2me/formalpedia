-- Prove2me | Theorems.Thm_ULHC_Edge_p_ne_q
-- name    : ULHC.Edge.p_ne_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:43:56.421909+00:00
-- url     : https://prove2.me/theorems/6d8a1c28-aea5-42f8-bc66-f823870466e1
-- title:
--   Edge: p ne q
-- statement:
--   The Edge construction uses the p ne q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L396-L398
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L396-L398

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.Edge.p_ne_q (e : Edge) : e.p ≠ e.q := by sorry
