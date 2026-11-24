-- Prove2me | Theorems.Thm_ULHC_outer1_side_nb_next
-- name    : ULHC.outer1_side_nb_next
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:38:52.220107+00:00
-- url     : https://prove2.me/theorems/8aea42e7-16a9-4a1b-a584-8837dc695a8d
-- title:
--   ULHC: outer1 side nb next
-- statement:
--   The ULHC construction uses the outer1 side nb next property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L47-L48
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L47-L48

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.outer1_side_nb_next : outer1 c s = sideEdge (nb (nb c s) (latA s)) s.opp := by sorry
