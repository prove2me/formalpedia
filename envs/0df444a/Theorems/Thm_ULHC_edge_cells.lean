-- Prove2me | Theorems.Thm_ULHC_edge_cells
-- name    : ULHC.edge_cells
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:42:17.123433+00:00
-- url     : https://prove2.me/theorems/2b30f894-f587-4508-864a-5909eab94b31
-- title:
--   ULHC: edge cells
-- statement:
--   The ULHC construction uses the edge cells property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TheoremA.lean#L181-L189
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TheoremA.lean#L181-L189

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.edge_cells (F : Finset Edge) (e : Edge) :
    ∃ sh sl, sideEdge e.hi sh = e ∧ nb e.hi sh = e.lo ∧ outArc F e.hi sh = !up F e ∧
      sideEdge e.lo sl = e ∧ nb e.lo sl = e.hi ∧ outArc F e.lo sl = up F e := by sorry
