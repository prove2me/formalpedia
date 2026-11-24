-- Prove2me | Theorems.Thm_ULHC_T_nextT_time_le
-- name    : ULHC.T.nextT_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:15:13.762303+00:00
-- url     : https://prove2.me/theorems/5732d312-7a0d-40c1-a6f9-e3bc92357eb3
-- title:
--   T: next T time le
-- statement:
--   The T construction uses the next T time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L204-L207
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L204-L207

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_Timed_MinPath
set_option autoImplicit true
open ULHC ULHC.T
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)

theorem ULHC.T.nextT_time_le (tbl : List (α × Option (ℕ × List α))) :
    (nextT NL mid tgt edgeT w tbl).time ≤ MP.nextCost NL mid tgt (fun a b => (edgeT a b).time) tbl := by sorry
