-- Prove2me | Theorems.Thm_ULHC_DWalk_parity
-- name    : ULHC.DWalk.parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:44:47.265286+00:00
-- url     : https://prove2.me/theorems/80bd405d-53fb-4f2a-a217-25e16e3557fc
-- title:
--   DWalk: parity
-- statement:
--   The DWalk construction uses the parity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Dual.lean#L113-L121
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Dual.lean#L113-L121

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F : Finset Edge}

theorem ULHC.DWalk.parity {a b : Pt} {B : Finset Edge} (h : DWalk V F a b B) (x : Pt)
    (hx : IsCell V x) :
    sidesIn B x % 2 = ((if x = a then 1 else 0) + (if x = b then 1 else 0)) % 2 := by sorry
