-- Prove2me | Theorems.Thm_ULHC_T_nextT_ret
-- name    : ULHC.T.nextT_ret
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:14:28.687634+00:00
-- url     : https://prove2.me/theorems/1659cb5d-c4f2-49dd-ba8f-71ab337b4f5c
-- title:
--   T: next T ret
-- statement:
--   The T construction uses the next T ret property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L125-L128
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L125-L128

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_Timed_MinPath
set_option autoImplicit true
open ULHC ULHC.T
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)

theorem ULHC.T.nextT_ret (tbl : List (α × Option (ℕ × List α))) :
    (nextT NL mid tgt edgeT w tbl).ret =
      MP.next NL mid tgt (fun a b => (edgeT a b).ret) w tbl := by sorry
