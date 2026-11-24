-- Prove2me | Theorems.Thm_ULHC_perp_bf
-- name    : ULHC.perp_bf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:32:17.31404+00:00
-- url     : https://prove2.me/theorems/30682abb-6937-4a26-a109-b7a96851d960
-- title:
--   ULHC: perp bf
-- statement:
--   The ULHC construction uses the perp bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L85-L91
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Touch.lean#L85-L91

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Touch
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.perp_bf {F : Finset Edge} {d : Pt} {s tf : Side} {P : Prop} (g1 : lat1 d tf ∈ F ↔ P)
    (g2 : lat2 d tf ∈ F ↔ P)
    (fl : (lat1 d tf = back d s ∧ lat2 d tf = front d s) ∨ (lat1 d tf = front d s ∧ lat2 d tf = back d s)) :
    back d s ∈ F ↔ front d s ∈ F := by sorry
