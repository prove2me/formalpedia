-- Prove2me | Theorems.Thm_ULHC_pot_eq_zero_of_left
-- name    : ULHC.pot_eq_zero_of_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:50.897661+00:00
-- url     : https://prove2.me/theorems/37dc9686-7027-43d9-90b6-26b7a44675e6
-- title:
--   ULHC: pot eq zero of left
-- statement:
--   The ULHC construction uses the pot eq zero of left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean#L78-L85
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean#L78-L85

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential
set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ}

theorem ULHC.pot_eq_zero_of_left {B : ℤ} (hB : ∀ e ∈ E, B < e.p.1) (c : Pt) (hc : c.1 ≤ B) :
    pot E w c = 0 := by sorry
