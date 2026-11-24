-- Prove2me | Theorems.Thm_ULHC_side_lat1_not_mem
-- name    : ULHC.side_lat1_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:38:57.579162+00:00
-- url     : https://prove2.me/theorems/e8df07c9-e3cf-4043-b694-547efb95811d
-- title:
--   ULHC: side lat1 not mem
-- statement:
--   The ULHC construction uses the side lat1 not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L91-L93
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L91-L93

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.side_lat1_not_mem (j m : ℕ) : lat1 (nb (cellJ c s j) (latA s)) s ∉ cellE (cellJ c s m) := by sorry
