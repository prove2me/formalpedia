-- Prove2me | Theorems.Thm_ULHC_T_stepT_ret
-- name    : ULHC.T.stepT_ret
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:10:39.584399+00:00
-- url     : https://prove2.me/theorems/0928e3b7-1e38-4565-aa3b-593388bfcfd1
-- title:
--   T: step T ret
-- statement:
--   The T construction uses the step T ret property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L114-L123
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L114-L123

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_Timed_MinPath
import Theorems.Thm_ULHC_Good_step

set_option autoImplicit true
open ULHC ULHC.T
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)

theorem ULHC.T.stepT_ret (tbl : List (α × Option (ℕ × List α))) (x : α) :
    (stepT NL mid tgt edgeT w tbl x).ret =
      MP.step NL mid tgt (fun a b => (edgeT a b).ret) w (fun y => MP.look y tbl) x := by sorry
