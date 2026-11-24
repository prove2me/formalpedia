-- Prove2me | Theorems.Thm_ULHC_pot_sub
-- name    : ULHC.pot_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:53.393883+00:00
-- url     : https://prove2.me/theorems/2e55f8f9-c8c4-4315-a417-92ad34c934d6
-- title:
--   ULHC: pot sub
-- statement:
--   The ULHC construction uses the pot sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean#L156-L158
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean#L156-L158

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential
set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ}

theorem ULHC.pot_sub (E : Finset Edge) (w₁ w₂ : Edge → ℤ) (c : Pt) :
    pot E (fun e => w₁ e - w₂ e) c = pot E w₁ c - pot E w₂ c := by sorry
