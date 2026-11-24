-- Prove2me | Theorems.Thm_ULHC_findT3_some
-- name    : ULHC.findT3_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:37:09.572122+00:00
-- url     : https://prove2.me/theorems/31f94ca5-e9f1-4024-9f82-491f449c865e
-- title:
--   ULHC: find T3 some
-- statement:
--   The ULHC construction uses the find T3 some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Algorithm.lean#L55-L65
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Algorithm.lean#L55-L65

import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_Algorithm
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.findT3_some {V : Finset Pt} {G : Finset Edge} (hGV : Inside V G) {d : Pt} {tf : Side}
    (h : findT3 V G = some (d, tf)) : IsCell V d ∧ back d tf ∈ G ∧ front d tf ∈ G ∧
      lat1 d tf ∉ G ∧ lat2 d tf ∉ G ∧ ¬ Conn G (back1 d tf) (front1 d tf) := by sorry
