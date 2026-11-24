-- Prove2me | Theorems.Thm_ULHC_D_around
-- name    : ULHC.D_around
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:14.084015+00:00
-- url     : https://prove2.me/theorems/30301c24-a1d7-4d64-a85a-1d63efb0f2d9
-- title:
--   ULHC: D around
-- statement:
--   The ULHC construction uses the D around property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L159-L171
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L159-L171

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
variable (hF : IsFactor V d F) (hH : IsFactor V d H)
include hF hH

theorem ULHC.D_around {a c : Pt} (ha : a ∉ V) (hc : Around a c) : D F H c = D F H a := by sorry
