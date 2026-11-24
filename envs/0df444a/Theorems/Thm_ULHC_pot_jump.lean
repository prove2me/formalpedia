-- Prove2me | Theorems.Thm_ULHC_pot_jump
-- name    : ULHC.pot_jump
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:19.526998+00:00
-- url     : https://prove2.me/theorems/44e94bb9-c853-441d-842a-8be58cbf8d61
-- title:
--   ULHC: pot jump
-- statement:
--   The ULHC construction uses the pot jump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean#L134-L139
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Potential.lean#L134-L139

import Definitions.Def_ULHC_Grid
import Definitions.Def_ULHC_Potential
set_option autoImplicit true
open ULHC
open Finset
variable {E : Finset Edge} {w : Edge → ℤ}

theorem ULHC.pot_jump (hS : Supp E w) (hbal : Balanced w) (e : Edge) :
    pot E w e.hi - pot E w e.lo = w e := by sorry
