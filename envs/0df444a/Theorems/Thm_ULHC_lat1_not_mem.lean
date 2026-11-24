-- Prove2me | Theorems.Thm_ULHC_lat1_not_mem
-- name    : ULHC.lat1_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:22.196734+00:00
-- url     : https://prove2.me/theorems/1f6526d8-a39f-4525-8461-c7627a202ab3
-- title:
--   ULHC: lat1 not mem
-- statement:
--   The ULHC construction uses the lat1 not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L269-L271
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L269-L271

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.lat1_not_mem {j m : ℕ} (h : j ≠ m) : lat1 (cellJ c s j) s ∉ cellE (cellJ c s m) := by sorry
