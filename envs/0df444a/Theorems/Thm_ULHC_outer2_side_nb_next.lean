-- Prove2me | Theorems.Thm_ULHC_outer2_side_nb_next
-- name    : ULHC.outer2_side_nb_next
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:27:38.912275+00:00
-- url     : https://prove2.me/theorems/39b01f43-f2b9-4a67-8f11-19f0760df96e
-- title:
--   ULHC: outer2 side nb next
-- statement:
--   The ULHC construction uses the outer2 side nb next property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L51-L52
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L51-L52

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.outer2_side_nb_next : outer2 c s = sideEdge (nb (nb c s) (latB s)) s.opp := by sorry
