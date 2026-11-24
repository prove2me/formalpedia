-- Prove2me | Theorems.Thm_ULHC_T_minPathLT_time_le
-- name    : ULHC.T.minPathLT_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:15:51.966985+00:00
-- url     : https://prove2.me/theorems/c58d0bc7-a366-4e4f-a8dc-254ca4e7891e
-- title:
--   T: min Path LT time le
-- statement:
--   The T construction uses the min Path LT time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L234-L242
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L234-L242

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_Timed_MinPath
set_option autoImplicit true
open ULHC ULHC.T
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)

theorem ULHC.T.minPathLT_time_le (srcT : α → TimeM Bool) :
    (minPathLT NL srcT mid tgt edgeT w).time ≤
      MP.minPathLCost NL mid tgt (fun a b => (edgeT a b).ret) w (fun a b => (edgeT a b).time)
        (fun x => (srcT x).time) := by sorry
