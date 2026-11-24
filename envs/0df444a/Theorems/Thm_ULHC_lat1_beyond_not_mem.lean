-- Prove2me | Theorems.Thm_ULHC_lat1_beyond_not_mem
-- name    : ULHC.lat1_beyond_not_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:32:02.402177+00:00
-- url     : https://prove2.me/theorems/0ff68f88-309e-4377-bc88-8df4957991af
-- title:
--   ULHC: lat1 beyond not mem
-- statement:
--   The ULHC construction uses the lat1 beyond not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L63-L64
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L63-L64

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.lat1_beyond_not_mem (n m : ℕ) (hm : m < n) :
    lat1 (cellJ c s n) s ∉ cellE (cellJ c s m) := by sorry
