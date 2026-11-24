-- Prove2me | Theorems.Thm_ULHC_DStep_parity
-- name    : ULHC.DStep.parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:45:18.812826+00:00
-- url     : https://prove2.me/theorems/42568c3d-5a3a-4bba-a776-db8f216f025c
-- title:
--   DStep: parity
-- statement:
--   The DStep construction uses the parity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Dual.lean#L90-L102
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Dual.lean#L90-L102

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}

theorem ULHC.DStep.parity {a d : Pt} {E : Finset Edge} (h : DStep V F a d E) (x : Pt) (hx : IsCell V x) :
    sidesIn E x % 2 = ((if x = a then 1 else 0) + (if x = d then 1 else 0)) % 2 := by sorry
