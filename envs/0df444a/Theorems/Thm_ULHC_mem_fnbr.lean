-- Prove2me | Theorems.Thm_ULHC_mem_fnbr
-- name    : ULHC.mem_fnbr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:46:58.365095+00:00
-- url     : https://prove2.me/theorems/0eb075ed-a9bd-407f-b343-ba64d7056731
-- title:
--   ULHC: mem fnbr
-- statement:
--   The ULHC construction uses the mem fnbr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Comp.lean#L41-L45
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Comp.lean#L41-L45

import Definitions.Def_ULHC_TwoFactor
import Definitions.Def_ULHC_Comp
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {F : Finset Edge}

theorem ULHC.mem_fnbr {u v : Pt} : v ∈ fnbr F u ↔ ∃ e ∈ F, (e.p = u ∨ e.q = u) ∧ other e u = v := by sorry
