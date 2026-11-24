-- Prove2me | Theorems.Thm_ULHC_T_ret_bind
-- name    : ULHC.T.ret_bind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:05:39.326102+00:00
-- url     : https://prove2.me/theorems/6e144b2f-0735-4091-97bd-315648cc9965
-- title:
--   T: ret bind
-- statement:
--   The T construction uses the ret bind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/TimeM.lean#L59-L59
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/TimeM.lean#L59-L59

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM
set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}

theorem ULHC.T.ret_bind (m : TimeM α) (f : α → TimeM β) : (m >>= f).ret = (f m.ret).ret := by sorry

attribute [defeq] ULHC.T.ret_bind
