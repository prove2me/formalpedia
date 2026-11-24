-- Prove2me | Theorems.Thm_ULHC_T_stepT_time_le
-- name    : ULHC.T.stepT_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:15:16.508147+00:00
-- url     : https://prove2.me/theorems/80d21c29-b24d-47bd-8227-d569a5113945
-- title:
--   T: step T time le
-- statement:
--   The T construction uses the step T time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L182-L202
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L182-L202

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_Timed_MinPath
set_option autoImplicit true
open ULHC ULHC.T
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)

theorem ULHC.T.stepT_time_le (tbl : List (α × Option (ℕ × List α))) (x : α) :
    (stepT NL mid tgt edgeT w tbl x).time ≤
      MP.stepCost NL mid tgt (fun a b => (edgeT a b).time) tbl x := by sorry
