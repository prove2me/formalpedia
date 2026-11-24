-- Prove2me | Theorems.Thm_ULHC_lat2_mem_self
-- name    : ULHC.lat2_mem_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:31:48.920864+00:00
-- url     : https://prove2.me/theorems/a0492e0b-a3a7-44f0-a72f-e0cb990872e4
-- title:
--   ULHC: lat2 mem self
-- statement:
--   The ULHC construction uses the lat2 mem self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L291-L292
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L291-L292

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.lat2_mem_self (j : ℕ) : lat2 (cellJ c s j) s ∈ cellE (cellJ c s j) := by sorry
