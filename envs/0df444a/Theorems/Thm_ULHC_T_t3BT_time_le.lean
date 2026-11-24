-- Prove2me | Theorems.Thm_ULHC_T_t3BT_time_le
-- name    : ULHC.T.t3BT_time_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:17:22.627857+00:00
-- url     : https://prove2.me/theorems/a452da59-e20c-4a9f-a6ae-10063c8fe7df
-- title:
--   T: t3 BT time le
-- statement:
--   The T construction uses the t3 BT time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Alg.lean#L187-L191
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Alg.lean#L187-L191

import Definitions.Def_ULHC_Timed_Strips
import Definitions.Def_ULHC_Timed_MinPath
import Definitions.Def_ULHC_Timed_TwoFactor
import Definitions.Def_ULHC_CostAlg
import Definitions.Def_ULHC_Timed_Alg
set_option autoImplicit true
open ULHC ULHC.T
open Finset

theorem ULHC.T.t3BT_time_le (V : Finset Pt) (G : Finset Edge) (d : Pt) (tf : Side) :
    (t3BT V G d tf).time ≤ t3BCost V G d tf := by sorry
