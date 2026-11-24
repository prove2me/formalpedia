-- Prove2me | Theorems.Thm_ULHC_ncomp_insert_merge
-- name    : ULHC.ncomp_insert_merge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:45.48701+00:00
-- url     : https://prove2.me/theorems/72ff95e6-3185-4792-8eee-4391a02f9e8f
-- title:
--   ULHC: ncomp insert merge
-- statement:
--   The ULHC construction uses the ncomp insert merge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L117-L207
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L117-L207

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.ncomp_insert_merge {V : Finset Pt} {F : Finset Edge} {e : Edge}
    (hu : e.p ∈ V) (hv : e.q ∈ V) (hn : ¬ Conn F e.p e.q) :
    ncomp V (insert e F) + 1 = ncomp V F := by sorry
