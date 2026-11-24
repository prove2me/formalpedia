-- Prove2me | Theorems.Thm_ULHC_T_stripScanT_time_le
-- name    : ULHC.T.stripScanT_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:13:44.456361+00:00
-- url     : https://prove2.me/theorems/7fb236ce-4d20-4470-89a1-467188c82fc1
-- title:
--   T: strip Scan T time le
-- statement:
--   The T construction uses the strip Scan T time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L223-L240
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L223-L240

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_Timed_Strips
set_option autoImplicit true
open ULHC ULHC.T
open Finset

theorem ULHC.T.stripScanT_time_le (V : Finset Pt) (F : Finset Edge) (c : Pt) (s : Side) :
    ∀ k j, (stripScanT V F c s k j).time ≤ stripScanCost V F c s k j
  := by sorry
