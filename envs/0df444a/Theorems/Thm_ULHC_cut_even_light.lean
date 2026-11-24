-- Prove2me | Theorems.Thm_ULHC_cut_even_light
-- name    : ULHC.cut_even_light
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:50:33.268797+00:00
-- url     : https://prove2.me/theorems/64048d02-2ec4-4f0f-885c-953de0d35a79
-- title:
--   ULHC: cut even light
-- statement:
--   The ULHC construction uses the cut even light property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Created.lean#L45-L57
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Created.lean#L45-L57

import Definitions.Def_ULHC_Reroute
import Definitions.Def_ULHC_Created
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.cut_even_light {V : Finset Pt} {F : Finset Edge} (S : Finset Pt)
    (hS : ∀ x y, Conn F x y → (x ∈ S ↔ y ∈ S)) :
    let B := (GE V).filter (Cut S)
    (∀ c, IsCell V c → sidesIn B c % 2 = 0) ∧ (∀ f ∈ B, f ∉ F) ∧
      ∀ f, f ∈ B ↔ IsEdge V f ∧ Cut S f := by sorry
