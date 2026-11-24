-- Prove2me | Theorems.Thm_ULHC_side2_back1
-- name    : ULHC.side2_back1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:58:01.868377+00:00
-- url     : https://prove2.me/theorems/7513b3be-ac7e-400b-968a-c95bab6255aa
-- title:
--   ULHC: side2 back1
-- statement:
--   The ULHC construction uses the side2 back1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L59-L60
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Near.lean#L59-L60

import Definitions.Def_ULHC_Enum
import Definitions.Def_ULHC_L57
import Definitions.Def_ULHC_Created
import Definitions.Def_ULHC_Near
set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)

theorem ULHC.side2_back1 : back1 (nb c (latB s)) s = back2 c s := by sorry
