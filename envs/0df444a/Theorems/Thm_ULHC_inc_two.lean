-- Prove2me | Theorems.Thm_ULHC_inc_two
-- name    : ULHC.inc_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:57:33.343799+00:00
-- url     : https://prove2.me/theorems/5674197d-402b-41ac-8839-115bd8891f3a
-- title:
--   ULHC: inc two
-- statement:
--   The ULHC construction uses the inc two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L442-L450
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L442-L450

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.inc_two {e : Edge} {y z u : Pt} (hy : e.p = y ∨ e.q = y) (hz : e.p = z ∨ e.q = z)
    (hne : y ≠ z) (hu : e.p = u ∨ e.q = u) : u = y ∨ u = z := by sorry
