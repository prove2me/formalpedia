-- Prove2me | Theorems.Thm_ULHC_outer1_side_nb
-- name    : ULHC.outer1_side_nb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:39:06.746124+00:00
-- url     : https://prove2.me/theorems/57583236-b05d-43c7-8937-4e259967325d
-- title:
--   ULHC: outer1 side nb
-- statement:
--   The ULHC construction uses the outer1 side nb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L39-L40
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L39-L40

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.outer1_side_nb : outer1 c s = sideEdge (nb c (latA s)) s := by sorry
