-- Prove2me | Theorems.Thm_ULHC_pot_jump_v
-- name    : ULHC.pot_jump_v
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:55.161267+00:00
-- url     : https://prove2.me/theorems/1792224f-cf38-4ca4-9747-fde82493de9e
-- title:
--   ULHC: pot jump v
-- statement:
--   The ULHC construction uses the pot jump v property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean#L53-L67
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean#L53-L67

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential
set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ}

theorem ULHC.pot_jump_v (hS : Supp E w) (c : Pt) :
    pot E w c - pot E w (c.1 - 1, c.2) = w ⟨.v, c⟩ := by sorry
