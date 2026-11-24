-- Prove2me | Theorems.Thm_ULHC_t3B_iff
-- name    : ULHC.t3B_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:37:27.871598+00:00
-- url     : https://prove2.me/theorems/3400cd27-18b9-4436-87bd-671b7c1c3e89
-- title:
--   ULHC: t3 B iff
-- statement:
--   The ULHC construction uses the t3 B iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Algorithm.lean#L47-L53
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Algorithm.lean#L47-L53

import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_Algorithm
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.t3B_iff {V : Finset Pt} {G : Finset Edge} (hGV : Inside V G) {d : Pt} (hd : IsCell V d)
    {tf : Side} : t3B V G d tf = true ↔ back d tf ∈ G ∧ front d tf ∈ G ∧ lat1 d tf ∉ G ∧
      lat2 d tf ∉ G ∧ ¬ Conn G (back1 d tf) (front1 d tf) := by sorry
