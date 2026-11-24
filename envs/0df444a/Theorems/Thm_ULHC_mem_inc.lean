-- Prove2me | Theorems.Thm_ULHC_mem_inc
-- name    : ULHC.mem_inc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:04.739842+00:00
-- url     : https://prove2.me/theorems/20073f98-a26b-40b9-80f2-fd1dacb1f574
-- title:
--   ULHC: mem inc
-- statement:
--   The ULHC construction uses the mem inc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L215-L218
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L215-L218

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.mem_inc {y : Pt} {e : Edge} : e ∈ inc y ↔ e.p = y ∨ e.q = y := by sorry
