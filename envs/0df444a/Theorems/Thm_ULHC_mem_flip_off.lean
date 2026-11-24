-- Prove2me | Theorems.Thm_ULHC_mem_flip_off
-- name    : ULHC.mem_flip_off
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:53:48.265924+00:00
-- url     : https://prove2.me/theorems/19287b84-15ac-4dae-84e4-08f7ba36d456
-- title:
--   ULHC: mem flip off
-- statement:
--   The ULHC construction uses the mem flip off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Cr2.lean#L76-L78
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Cr2.lean#L76-L78

import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Cr2
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {G : Finset Edge}

theorem ULHC.mem_flip_off {G : Finset Edge} {u : Pt} {e : Edge} (h : e ∉ cellE u) :
    e ∈ flip G u ↔ e ∈ G := by sorry
