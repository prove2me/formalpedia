-- Prove2me | Theorems.Thm_ULHC_T_cclsT_time_le
-- name    : ULHC.T.cclsT_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:39:59.874802+00:00
-- url     : https://prove2.me/theorems/428df3a6-f52a-4520-82ef-3ccf9905531c
-- title:
--   T: ccls T time le
-- statement:
--   The T construction uses the ccls T time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Conn.lean#L117-L121
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Conn.lean#L117-L121

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_Timed_Conn
set_option autoImplicit true
open ULHC ULHC.T
open Finset

theorem ULHC.T.cclsT_time_le (V : Finset Pt) (F : Finset Edge) (x : Pt) :
    (cclsT V F x).time ≤ cclsCost V F x := by sorry
