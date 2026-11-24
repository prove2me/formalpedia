-- Prove2me | Theorems.Thm_ULHC_lat2_not_mem
-- name    : ULHC.lat2_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:19:43.048499+00:00
-- url     : https://prove2.me/theorems/96aee89f-d6bd-4b1d-a413-027c75bb0c11
-- title:
--   ULHC: lat2 not mem
-- statement:
--   The ULHC construction uses the lat2 not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L273-L275
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L273-L275

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.lat2_not_mem {j m : ℕ} (h : j ≠ m) : lat2 (cellJ c s j) s ∉ cellE (cellJ c s m) := by sorry
