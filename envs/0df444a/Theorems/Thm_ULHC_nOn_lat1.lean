-- Prove2me | Theorems.Thm_ULHC_nOn_lat1
-- name    : ULHC.nOn_lat1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:41:00.337581+00:00
-- url     : https://prove2.me/theorems/3fc34cc7-6ebd-4ce5-ba0e-08efe5ef29c4
-- title:
--   ULHC: n On lat1
-- statement:
--   The ULHC construction uses the n On lat1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L734-L742
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L734-L742

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.nOn_lat1 {n j : ℕ} (hj : j < n) : nOn c s n (lat1 (cellJ c s j) s) = 1 := by sorry
