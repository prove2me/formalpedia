-- Prove2me | Theorems.Thm_ULHC_pot_around
-- name    : ULHC.pot_around
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:51:58.320875+00:00
-- url     : https://prove2.me/theorems/ca60b0cb-4029-4ffd-b6e1-302f3cdc8880
-- title:
--   ULHC: pot around
-- statement:
--   The ULHC construction uses the pot around property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Planar.lean#L102-L113
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Planar.lean#L102-L113

import Definitions.Def_ULHC_Conn
import Definitions.Def_ULHC_Planar
set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ} (hS : Supp E w) (hb : Balanced w)
include hS hb

theorem ULHC.pot_around {z : Pt} (h0 : w (eR z) = 0 ∧ w (eU z) = 0 ∧ w (eL z) = 0 ∧ w (eD z) = 0)
    {c : Pt} (hc : Around z c) : pot E w c = pot E w z := by sorry
