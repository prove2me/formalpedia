-- Prove2me | Theorems.Thm_ULHC_notTypeIII_of_no
-- name    : ULHC.notTypeIII_of_no
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:45:59.986461+00:00
-- url     : https://prove2.me/theorems/28da60ed-b01a-4aa8-927c-8b11e7adb135
-- title:
--   ULHC: not Type III of no
-- statement:
--   The ULHC construction uses the not Type III of no property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2Seq.lean#L118-L123
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/V2Seq.lean#L118-L123

import Definitions.Def_ULHC_Dual
import Definitions.Def_ULHC_V2Seq
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {H : Finset Edge}
  (hs : Solid V) (hH : Deg2 V H) (hHam : ncomp V H = 1)
include hs hH hHam
omit hs hH hHam

theorem ULHC.notTypeIII_of_no {F : Finset Edge} (h : ¬ NoTypeIII V F) :
    ∃ d, IsCell V d ∧ ¬ NotTypeIII V F d := by sorry
