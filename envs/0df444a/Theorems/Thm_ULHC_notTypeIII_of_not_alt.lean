-- Prove2me | Theorems.Thm_ULHC_notTypeIII_of_not_alt
-- name    : ULHC.notTypeIII_of_not_alt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:43:42.125323+00:00
-- url     : https://prove2.me/theorems/a0be6adf-be06-4c09-beae-2c773e075b51
-- title:
--   ULHC: not Type III of not alt
-- statement:
--   The ULHC construction uses the not Type III of not alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L117-L118
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L117-L118

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.notTypeIII_of_not_alt {V : Finset Pt} {F : Finset Edge} {d : Pt} (h : ¬ Alt F d) :
    NotTypeIII V F d := by sorry
