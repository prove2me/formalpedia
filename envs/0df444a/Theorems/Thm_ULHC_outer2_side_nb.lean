-- Prove2me | Theorems.Thm_ULHC_outer2_side_nb
-- name    : ULHC.outer2_side_nb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:38:57.061896+00:00
-- url     : https://prove2.me/theorems/e3b08732-a1dc-4a06-a99e-7fd0e78fb3ae
-- title:
--   ULHC: outer2 side nb
-- statement:
--   The ULHC construction uses the outer2 side nb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L42-L43
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L42-L43

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.outer2_side_nb : outer2 c s = sideEdge (nb c (latB s)) s := by sorry
