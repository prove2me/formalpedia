-- Prove2me | Theorems.Thm_ULHC_pot_add
-- name    : ULHC.pot_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:00:14.207197+00:00
-- url     : https://prove2.me/theorems/0769b7b6-e5bb-4de2-a82f-f31dfcc1d2f8
-- title:
--   ULHC: pot add
-- statement:
--   The ULHC construction uses the pot add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean#L152-L154
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean#L152-L154

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential
set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ}

theorem ULHC.pot_add (E : Finset Edge) (w₁ w₂ : Edge → ℤ) (c : Pt) :
    pot E (fun e => w₁ e + w₂ e) c = pot E w₁ c + pot E w₂ c := by sorry
