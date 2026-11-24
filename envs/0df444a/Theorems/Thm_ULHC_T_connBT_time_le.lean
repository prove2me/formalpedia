-- Prove2me | Theorems.Thm_ULHC_T_connBT_time_le
-- name    : ULHC.T.connBT_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:31:06.612925+00:00
-- url     : https://prove2.me/theorems/325f5909-1c15-49ef-b625-e1562521853b
-- title:
--   T: conn BT time le
-- statement:
--   The T construction uses the conn BT time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Conn.lean#L127-L131
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Conn.lean#L127-L131

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_Timed_Conn
set_option autoImplicit true
open ULHC ULHC.T
open Finset

theorem ULHC.T.connBT_time_le (V : Finset Pt) (F : Finset Edge) (x y : Pt) :
    (connBT V F x y).time ≤ connBCost V F x := by sorry
