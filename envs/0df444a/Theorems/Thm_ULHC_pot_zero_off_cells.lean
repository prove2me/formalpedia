-- Prove2me | Theorems.Thm_ULHC_pot_zero_off_cells
-- name    : ULHC.pot_zero_off_cells
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:51:20.238207+00:00
-- url     : https://prove2.me/theorems/5644b952-c337-43f3-9fbc-11af3d8016cb
-- title:
--   ULHC: pot zero off cells
-- statement:
--   The ULHC construction uses the pot zero off cells property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L281-L296
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L281-L296

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {E : Finset Edge} {w : Edge → ℤ}
  (hS : Supp E w) (hb : Balanced w) (hE : ∀ e ∈ E, e.p ∈ V ∧ e.q ∈ V)
include hS hb hE

theorem ULHC.pot_zero_off_cells (hs : Solid V) {c : Pt} (hc : ¬ IsCell V c) : pot E w c = 0 := by sorry
