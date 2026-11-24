-- Prove2me | Theorems.Thm_ULHC_other_ne
-- name    : ULHC.other_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:09.496783+00:00
-- url     : https://prove2.me/theorems/2413af96-8cd1-495f-bf58-7525b32c9523
-- title:
--   ULHC: other ne
-- statement:
--   The ULHC construction uses the other ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L416-L422
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L416-L422

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.other_ne {e : Edge} {y : Pt} (hy : e.p = y ∨ e.q = y) : other e y ≠ y := by sorry
