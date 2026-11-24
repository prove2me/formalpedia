-- Prove2me | Theorems.Thm_ULHC_typeIII_strip
-- name    : ULHC.typeIII_strip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:49:26.598423+00:00
-- url     : https://prove2.me/theorems/96dc069f-c790-4b35-bea4-36cef9a097c0
-- title:
--   ULHC: type III strip
-- statement:
--   The ULHC construction uses the type III strip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TheoremA.lean#L193-L204
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TheoremA.lean#L193-L204

import Definitions.Def_ULHC_Phase2
import Definitions.Def_ULHC_TheoremA
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.typeIII_strip {V : Finset Pt} {F : Finset Edge} (h : ¬ NoTypeIII V F) :
    ∃ σ : StripSpec, ValidStrip V F σ ∧ σ.n % 2 = 1 := by sorry
