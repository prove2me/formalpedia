-- Prove2me | Theorems.Thm_ULHC_other_inc
-- name    : ULHC.other_inc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:49:53.818979+00:00
-- url     : https://prove2.me/theorems/1a3b7231-d483-47e4-934c-c058b20547af
-- title:
--   ULHC: other inc
-- statement:
--   The ULHC construction uses the other inc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L413-L414
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L413-L414

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.other_inc {e : Edge} {y : Pt} : e.p = other e y ∨ e.q = other e y := by sorry
