-- Prove2me | Theorems.Thm_ULHC_nOn_lat2
-- name    : ULHC.nOn_lat2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:41:11.18281+00:00
-- url     : https://prove2.me/theorems/0063c503-a1b6-410f-bafb-dabeddce7c6a
-- title:
--   ULHC: n On lat2
-- statement:
--   The ULHC construction uses the n On lat2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L744-L752
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L744-L752

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.nOn_lat2 {n j : ℕ} (hj : j < n) : nOn c s n (lat2 (cellJ c s j) s) = 1 := by sorry
