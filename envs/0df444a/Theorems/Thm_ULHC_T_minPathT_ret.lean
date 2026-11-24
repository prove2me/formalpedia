-- Prove2me | Theorems.Thm_ULHC_T_minPathT_ret
-- name    : ULHC.T.minPathT_ret
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:15:50.758399+00:00
-- url     : https://prove2.me/theorems/8a4f0921-f968-49e2-b583-06a4a3e0b157
-- title:
--   T: min Path T ret
-- statement:
--   The T construction uses the min Path T ret property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L147-L151
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L147-L151

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_Timed_MinPath
set_option autoImplicit true
open ULHC ULHC.T
variable {α : Type} [DecidableEq α]

theorem ULHC.T.minPathT_ret {β : Type} [LinearOrder β] (N : Finset β) (srcT : β → TimeM Bool)
    (mid tgt : β → Bool) (edgeT : β → β → TimeM Bool) (w : β → ℕ) :
    (minPathT N srcT mid tgt edgeT w).ret =
      MP.minPath N (fun x => (srcT x).ret) mid tgt (fun a b => (edgeT a b).ret) w := by sorry
