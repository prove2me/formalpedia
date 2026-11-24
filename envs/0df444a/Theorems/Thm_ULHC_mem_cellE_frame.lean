-- Prove2me | Theorems.Thm_ULHC_mem_cellE_frame
-- name    : ULHC.mem_cellE_frame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:32:57.033725+00:00
-- url     : https://prove2.me/theorems/02d57703-0a1f-4385-ab52-a3b6cff69c31
-- title:
--   ULHC: mem cell E frame
-- statement:
--   The ULHC construction uses the mem cell E frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Stacked.lean#L157-L159
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Stacked.lean#L157-L159

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Stacked
set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)

theorem ULHC.mem_cellE_frame (g : Edge) :
    g ∈ cellE c ↔ g = back c s ∨ g = front c s ∨ g = lat1 c s ∨ g = lat2 c s := by sorry
