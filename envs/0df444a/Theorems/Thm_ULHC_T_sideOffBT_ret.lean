-- Prove2me | Theorems.Thm_ULHC_T_sideOffBT_ret
-- name    : ULHC.T.sideOffBT_ret
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:12:39.260448+00:00
-- url     : https://prove2.me/theorems/da3e7f82-724d-4d11-933e-ac3acbd844f5
-- title:
--   T: side Off BT ret
-- statement:
--   The T construction uses the side Off BT ret property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L178-L179
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/Strips.lean#L178-L179

import Definitions.Def_ULHC_Timed_Conn
import Definitions.Def_ULHC_CostStrips
import Definitions.Def_ULHC_Timed_Strips
set_option autoImplicit true
open ULHC ULHC.T
open Finset

theorem ULHC.T.sideOffBT_ret (b c : StripSpec) : (sideOffBT b c).ret = sideOffB b c := by sorry
