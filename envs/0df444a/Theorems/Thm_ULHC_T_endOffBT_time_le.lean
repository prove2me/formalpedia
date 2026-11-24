-- Prove2me | Theorems.Thm_ULHC_T_endOffBT_time_le
-- name    : ULHC.T.endOffBT_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:14:25.197349+00:00
-- url     : https://prove2.me/theorems/f39a175a-d3a1-4a48-a0d7-6b8354d380d1
-- title:
--   T: end Off BT time le
-- statement:
--   The T construction uses the end Off BT time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L338-L344
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L338-L344

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_Timed_Strips
set_option autoImplicit true
open ULHC ULHC.T
open Finset

theorem ULHC.T.endOffBT_time_le (b c : StripSpec) : (endOffBT b c).time ≤ endOffBCost := by sorry
