-- Prove2me | Theorems.Thm_ULHC_pot_jump_h
-- name    : ULHC.pot_jump_h
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:44.274715+00:00
-- url     : https://prove2.me/theorems/d15a92b2-27a9-4f69-a583-bda83a0b5ddf
-- title:
--   ULHC: pot jump h
-- statement:
--   The ULHC construction uses the pot jump h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean#L89-L130
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean#L89-L130

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential
set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ}

theorem ULHC.pot_jump_h (hS : Supp E w) (hbal : Balanced w) (c : Pt) :
    pot E w c - pot E w (c.1, c.2 - 1) = w ⟨.h, c⟩ := by sorry
