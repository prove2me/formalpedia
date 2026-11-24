-- Prove2me | Theorems.Thm_ULHC_T_gsrcT_time_le
-- name    : ULHC.T.gsrcT_time_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:14:33.389959+00:00
-- url     : https://prove2.me/theorems/846524f1-dbf6-4f28-b247-4a97cd038bfe
-- title:
--   T: gsrc T time le
-- statement:
--   The T construction uses the gsrc T time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L387-L391
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L387-L391

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_Timed_Strips
set_option autoImplicit true
open ULHC ULHC.T
open Finset

theorem ULHC.T.gsrcT_time_le (V : Finset Pt) (G : Finset Edge) (x : Node) :
    (gsrcT V G x).time ≤ gsrcCost V G x := by sorry
