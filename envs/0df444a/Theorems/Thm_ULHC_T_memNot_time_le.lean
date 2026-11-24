-- Prove2me | Theorems.Thm_ULHC_T_memNot_time_le
-- name    : ULHC.T.memNot_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:40:26.014879+00:00
-- url     : https://prove2.me/theorems/c63a2daf-7763-4f50-91cc-7b9659297eda
-- title:
--   T: mem Not time le
-- statement:
--   The T construction uses the mem Not time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L295-L297
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L295-L297

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_Timed_Strips
set_option autoImplicit true
open ULHC ULHC.T
open Finset

theorem ULHC.T.memNot_time_le (e : Edge) (S : Finset Edge) :
    (do let m ← memT e S; pure (!m) : TimeM Bool).time ≤ 1 := by sorry
