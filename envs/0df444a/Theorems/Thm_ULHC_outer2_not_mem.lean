-- Prove2me | Theorems.Thm_ULHC_outer2_not_mem
-- name    : ULHC.outer2_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:28:51.155407+00:00
-- url     : https://prove2.me/theorems/a996beb0-b6ba-4b04-885e-7babb4242785
-- title:
--   ULHC: outer2 not mem
-- statement:
--   The ULHC construction uses the outer2 not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L59-L61
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L59-L61

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.outer2_not_mem (j m : ℕ) : outer2 (cellJ c s j) s ∉ cellE (cellJ c s m) := by sorry
