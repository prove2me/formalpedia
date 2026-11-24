-- Prove2me | Theorems.Thm_ULHC_stk_lat2_dn
-- name    : ULHC.stk_lat2_dn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:55:01.770267+00:00
-- url     : https://prove2.me/theorems/3574ffc3-3284-4cbe-aa8a-371064bf6f97
-- title:
--   ULHC: stk lat2 dn
-- statement:
--   The ULHC construction uses the stk lat2 dn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Stacked.lean#L185-L189
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Stacked.lean#L185-L189

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Stacked
set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)

theorem ULHC.stk_lat2_dn : lat2 c s ∉ cellE (nb c s) := by sorry
