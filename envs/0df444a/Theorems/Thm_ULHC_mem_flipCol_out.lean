-- Prove2me | Theorems.Thm_ULHC_mem_flipCol_out
-- name    : ULHC.mem_flipCol_out
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:01:58.983048+00:00
-- url     : https://prove2.me/theorems/f73d7fd0-40e1-40f7-a71d-afa5523a1ff0
-- title:
--   ULHC: mem flip Col out
-- statement:
--   The ULHC construction uses the mem flip Col out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L273-L276
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L273-L276

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.mem_flipCol_out {F : Finset Edge} {c : Pt} {s : Side} {n : ℕ} {e : Edge}
    (h : ∀ j < n, e ∉ cellE (cellJ c s j)) : e ∈ flipCol F c s n ↔ e ∈ F := by sorry
