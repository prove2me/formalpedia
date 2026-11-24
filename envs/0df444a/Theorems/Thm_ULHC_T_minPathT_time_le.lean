-- Prove2me | Theorems.Thm_ULHC_T_minPathT_time_le
-- name    : ULHC.T.minPathT_time_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:15:58.989139+00:00
-- url     : https://prove2.me/theorems/3a62c3dc-65d7-475b-bddb-553e76428d0c
-- title:
--   T: min Path T time le
-- statement:
--   The T construction uses the min Path T time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L246-L253
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L246-L253

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_Timed_MinPath
set_option autoImplicit true
open ULHC ULHC.T
variable {α : Type} [DecidableEq α]

theorem ULHC.T.minPathT_time_le {β : Type} [LinearOrder β] (N : Finset β) (srcT : β → TimeM Bool)
    (mid tgt : β → Bool) (edgeT : β → β → TimeM Bool) (w : β → ℕ) :
    (minPathT N srcT mid tgt edgeT w).time ≤
      MP.minPathCost N mid tgt (fun a b => (edgeT a b).ret) w (fun a b => (edgeT a b).time)
        (fun x => (srcT x).time) := by sorry
