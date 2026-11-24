-- Prove2me | Theorems.Thm_ULHC_deg_erase
-- name    : ULHC.deg_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:42:21.160811+00:00
-- url     : https://prove2.me/theorems/f3e1ee5d-5c68-41e3-a377-b6d96574fae4
-- title:
--   ULHC: deg erase
-- statement:
--   The ULHC construction uses the deg erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L237-L245
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L237-L245

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.deg_erase {F : Finset Edge} {e : Edge} (he : e ∈ F) (y : Pt) :
    deg (F.erase e) y + (if e.p = y ∨ e.q = y then 1 else 0) = deg F y := by sorry
