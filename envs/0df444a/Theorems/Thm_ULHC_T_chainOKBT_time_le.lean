-- Prove2me | Theorems.Thm_ULHC_T_chainOKBT_time_le
-- name    : ULHC.T.chainOKBT_time_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:14:27.748489+00:00
-- url     : https://prove2.me/theorems/1e476022-55d9-4883-9918-5f5b25536bf9
-- title:
--   T: chain OKBT time le
-- statement:
--   The T construction uses the chain OKBT time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L368-L385
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L368-L385

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_Timed_Strips
set_option autoImplicit true
open ULHC ULHC.T
open Finset

theorem ULHC.T.chainOKBT_time_le (b c : StripSpec) : (chainOKBT b c).time ≤ chainOKBCost c := by sorry
