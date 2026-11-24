-- Prove2me | Theorems.Thm_ULHC_T_validBT_time_le
-- name    : ULHC.T.validBT_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:13:43.229398+00:00
-- url     : https://prove2.me/theorems/bced7132-965f-43cb-aef0-87c52eeecef4
-- title:
--   T: valid BT time le
-- statement:
--   The T construction uses the valid BT time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L288-L293
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L288-L293

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_Timed_Strips
set_option autoImplicit true
open ULHC ULHC.T
open Finset

theorem ULHC.T.validBT_time_le (V : Finset Pt) (F : Finset Edge) (σ : StripSpec) :
    (validBT V F σ).time ≤ validBCost V F σ := by sorry
