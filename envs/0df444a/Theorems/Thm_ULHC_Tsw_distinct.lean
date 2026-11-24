-- Prove2me | Theorems.Thm_ULHC_Tsw_distinct
-- name    : ULHC.Tsw_distinct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:49:27.139729+00:00
-- url     : https://prove2.me/theorems/bc2e96af-03d3-462d-84b9-323df2296db0
-- title:
--   ULHC: Tsw distinct
-- statement:
--   The ULHC construction uses the Tsw distinct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L70-L81
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Reroute.lean#L70-L81

import Definitions.Def_ULHC_V2Seq
import Definitions.Def_ULHC_Reroute
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.Tsw_distinct (j : ℕ) :
    lat1 (cellJ c s j) s ≠ lat2 (cellJ c s j) s ∧ lat1 (cellJ c s j) s ≠ lat1 (cellJ c s (j + 1)) s ∧
    lat1 (cellJ c s j) s ≠ lat2 (cellJ c s (j + 1)) s ∧ lat1 (cellJ c s j) s ≠ outer1 (cellJ c s j) s ∧
    lat1 (cellJ c s j) s ≠ outer2 (cellJ c s j) s ∧
    lat2 (cellJ c s j) s ≠ lat1 (cellJ c s (j + 1)) s ∧ lat2 (cellJ c s j) s ≠ lat2 (cellJ c s (j + 1)) s ∧
    lat2 (cellJ c s j) s ≠ outer1 (cellJ c s j) s ∧ lat2 (cellJ c s j) s ≠ outer2 (cellJ c s j) s ∧
    lat1 (cellJ c s (j + 1)) s ≠ lat2 (cellJ c s (j + 1)) s ∧
    lat1 (cellJ c s (j + 1)) s ≠ outer1 (cellJ c s j) s ∧ lat1 (cellJ c s (j + 1)) s ≠ outer2 (cellJ c s j) s ∧
    lat2 (cellJ c s (j + 1)) s ≠ outer1 (cellJ c s j) s ∧ lat2 (cellJ c s (j + 1)) s ≠ outer2 (cellJ c s j) s ∧
    outer1 (cellJ c s j) s ≠ outer2 (cellJ c s j) s := by sorry
