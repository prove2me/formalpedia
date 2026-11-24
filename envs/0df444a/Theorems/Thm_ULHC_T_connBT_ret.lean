-- Prove2me | Theorems.Thm_ULHC_T_connBT_ret
-- name    : ULHC.T.connBT_ret
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:10:36.811166+00:00
-- url     : https://prove2.me/theorems/ad49f213-21c0-4f4b-9ca9-1d05e9c067fe
-- title:
--   T: conn BT ret
-- statement:
--   The T construction uses the conn BT ret property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Conn.lean#L123-L125
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Conn.lean#L123-L125

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_Timed_Conn
set_option autoImplicit true
open ULHC ULHC.T
open Finset

theorem ULHC.T.connBT_ret (V : Finset Pt) (F : Finset Edge) (x y : Pt) :
    (connBT V F x y).ret = connB V F x y := by sorry
