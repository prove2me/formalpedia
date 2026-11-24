-- Prove2me | Theorems.Thm_ULHC_T_minPathLT_ret
-- name    : ULHC.T.minPathLT_ret
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:15:39.029287+00:00
-- url     : https://prove2.me/theorems/ebe91824-9d13-49fe-b237-16a5a3e74d7a
-- title:
--   T: min Path LT ret
-- statement:
--   The T construction uses the min Path LT ret property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L140-L143
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L140-L143

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_Timed_MinPath
set_option autoImplicit true
open ULHC ULHC.T
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)

theorem ULHC.T.minPathLT_ret (srcT : α → TimeM Bool) :
    (minPathLT NL srcT mid tgt edgeT w).ret =
      MP.minPathL NL (fun x => (srcT x).ret) mid tgt (fun a b => (edgeT a b).ret) w := by sorry
