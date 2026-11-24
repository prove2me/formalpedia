-- Prove2me | Theorems.Thm_ULHC_T_time_bind
-- name    : ULHC.T.time_bind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:06:24.455013+00:00
-- url     : https://prove2.me/theorems/e5b4101b-799d-4fdd-aceb-4e4b9a9b8f17
-- title:
--   T: time bind
-- statement:
--   The T construction uses the time bind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/TimeM.lean#L60-L61
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/TimeM.lean#L60-L61

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM
set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}

theorem ULHC.T.time_bind (m : TimeM α) (f : α → TimeM β) :
    (m >>= f).time = m.time + (f m.ret).time := by sorry

attribute [defeq] ULHC.T.time_bind
