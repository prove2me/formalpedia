-- Prove2me | Theorems.Thm_ULHC_T_notEndBT_time_le
-- name    : ULHC.T.notEndBT_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:14:31.627419+00:00
-- url     : https://prove2.me/theorems/ea54eca5-ecf0-4b58-8773-7daa8d4440b5
-- title:
--   T: not End BT time le
-- statement:
--   The T construction uses the not End BT time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L346-L352
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L346-L352

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_Timed_Strips
set_option autoImplicit true
open ULHC ULHC.T
open Finset

theorem ULHC.T.notEndBT_time_le (b c : StripSpec) : (notEndBT b c).time ≤ notEndBCost c := by sorry
