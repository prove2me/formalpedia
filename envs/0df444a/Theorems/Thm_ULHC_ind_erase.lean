-- Prove2me | Theorems.Thm_ULHC_ind_erase
-- name    : ULHC.ind_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:57.020381+00:00
-- url     : https://prove2.me/theorems/938a69f4-0a86-49f2-affa-5080b88ab586
-- title:
--   ULHC: ind erase
-- statement:
--   The ULHC construction uses the ind erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L220-L225
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L220-L225

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.ind_erase {F : Finset Edge} {e : Edge} (he : e ∈ F) (g : Edge) :
    ind (F.erase e) g + (if g = e then 1 else 0) = ind F g := by sorry
