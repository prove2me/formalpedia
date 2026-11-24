-- Prove2me | Theorems.Thm_ULHC_sidesIn_symmDiff
-- name    : ULHC.sidesIn_symmDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:31:39.271442+00:00
-- url     : https://prove2.me/theorems/a3e8ed3f-3598-41c4-a775-e0b300b3a23f
-- title:
--   ULHC: sides In symm Diff
-- statement:
--   The ULHC construction uses the sides In symm Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Dual.lean#L30-L37
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Dual.lean#L30-L37

import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Dual
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.sidesIn_symmDiff (A B : Finset Edge) (c : Pt) :
    sidesIn (symmDiff A B) c % 2 = (sidesIn A c + sidesIn B c) % 2 := by sorry
