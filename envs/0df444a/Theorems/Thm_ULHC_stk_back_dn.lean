-- Prove2me | Theorems.Thm_ULHC_stk_back_dn
-- name    : ULHC.stk_back_dn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:06:37.68002+00:00
-- url     : https://prove2.me/theorems/c323f0ea-e8c7-4656-be5e-500d97b15397
-- title:
--   ULHC: stk back dn
-- statement:
--   The ULHC construction uses the stk back dn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Stacked.lean#L191-L195
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Stacked.lean#L191-L195

import Definitions.Def_ULHC_Near
import Definitions.Def_ULHC_Stacked
set_option autoImplicit true
open ULHC
open Finset
variable (c : Pt) (s : Side)

theorem ULHC.stk_back_dn : back c s ∉ cellE (nb c s) := by sorry
