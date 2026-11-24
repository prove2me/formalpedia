-- Prove2me | Theorems.Thm_ULHC_T_pickSrcT_time_le
-- name    : ULHC.T.pickSrcT_time_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:15:39.299707+00:00
-- url     : https://prove2.me/theorems/35882762-c212-475f-a38a-502ce0743827
-- title:
--   T: pick Src T time le
-- statement:
--   The T construction uses the pick Src T time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L219-L232
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L219-L232

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_Timed_MinPath
set_option autoImplicit true
open ULHC ULHC.T
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)

theorem ULHC.T.pickSrcT_time_le (srcT : α → TimeM Bool) (tbl : List (α × Option (ℕ × List α))) :
    (pickSrcT NL srcT tbl).time ≤ MP.pickSrcCost NL (fun x => (srcT x).time) tbl := by sorry
