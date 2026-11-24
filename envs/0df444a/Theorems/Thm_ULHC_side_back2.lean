-- Prove2me | Theorems.Thm_ULHC_side_back2
-- name    : ULHC.side_back2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:29:39.381015+00:00
-- url     : https://prove2.me/theorems/581c7903-c166-444e-af88-79901e1176d5
-- title:
--   ULHC: side back2
-- statement:
--   The ULHC construction uses the side back2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L68-L69
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/L57.lean#L68-L69

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
set_option autoImplicit true
open ULHC
open Finset Classical
variable (c : Pt) (s : Side)

theorem ULHC.side_back2 : back2 (nb c (latA s)) s = back1 c s := by sorry
