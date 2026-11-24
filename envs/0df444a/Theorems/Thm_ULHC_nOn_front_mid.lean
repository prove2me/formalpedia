-- Prove2me | Theorems.Thm_ULHC_nOn_front_mid
-- name    : ULHC.nOn_front_mid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:43:00.022686+00:00
-- url     : https://prove2.me/theorems/43d40282-9fdb-48bc-9020-e761d356affd
-- title:
--   ULHC: n On front mid
-- statement:
--   The ULHC construction uses the n On front mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L778-L789
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Chain.lean#L778-L789

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.nOn_front_mid {n j : ℕ} (hj : j + 1 < n) : nOn c s n (front (cellJ c s j) s) = 2 := by sorry
