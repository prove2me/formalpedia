-- Prove2me | Theorems.Thm_ULHC_T_sideOffBT_time_le
-- name    : ULHC.T.sideOffBT_time_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:14:19.55062+00:00
-- url     : https://prove2.me/theorems/92baa14e-8af9-49be-b4ff-f2e9f50a07a3
-- title:
--   T: side Off BT time le
-- statement:
--   The T construction uses the side Off BT time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L299-L326
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L299-L326

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_Timed_Strips
set_option autoImplicit true
open ULHC ULHC.T
open Finset

theorem ULHC.T.sideOffBT_time_le (b c : StripSpec) : (sideOffBT b c).time ≤ sideOffBCost b c := by sorry
