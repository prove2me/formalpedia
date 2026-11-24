-- Prove2me | Theorems.Thm_ULHC_pot_eq_sum_ite
-- name    : ULHC.pot_eq_sum_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:10.449843+00:00
-- url     : https://prove2.me/theorems/a4152c78-f23a-462f-9b4d-43f286119faf
-- title:
--   ULHC: pot eq sum ite
-- statement:
--   The ULHC construction uses the pot eq sum ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean#L47-L49
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean#L47-L49

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential
set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ}

theorem ULHC.pot_eq_sum_ite (c : Pt) :
    pot E w c = ∑ e ∈ E, if RowSel c e then w e else 0 := by sorry
