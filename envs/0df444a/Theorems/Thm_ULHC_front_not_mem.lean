-- Prove2me | Theorems.Thm_ULHC_front_not_mem
-- name    : ULHC.front_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:23:43.236874+00:00
-- url     : https://prove2.me/theorems/9857730f-3218-4861-bb69-4a0c9d33f5e7
-- title:
--   ULHC: front not mem
-- statement:
--   The ULHC construction uses the front not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L277-L280
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L277-L280

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.front_not_mem {j m : ℕ} (h1 : j ≠ m) (h2 : m ≠ j + 1) :
    front (cellJ c s j) s ∉ cellE (cellJ c s m) := by sorry
