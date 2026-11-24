-- Prove2me | Theorems.Thm_ULHC_TF_mem_inc4
-- name    : ULHC.TF.mem_inc4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:35:43.540118+00:00
-- url     : https://prove2.me/theorems/0f58b7c8-6d38-4405-9ae3-748a6dcaebdc
-- title:
--   TF: mem inc4
-- statement:
--   The TF construction uses the mem inc4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L149-L152
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/TwoFactor.lean#L149-L152

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_TwoFactor
set_option autoImplicit true
open ULHC
open Finset
open ULHC.TF

theorem ULHC.TF.mem_inc4 {e : Edge} {z : Pt} : e ∈ inc4 z ↔ e.p = z ∨ e.q = z := by sorry
