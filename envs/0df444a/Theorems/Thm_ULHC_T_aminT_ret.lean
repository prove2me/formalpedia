-- Prove2me | Theorems.Thm_ULHC_T_aminT_ret
-- name    : ULHC.T.aminT_ret
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:11:00.890126+00:00
-- url     : https://prove2.me/theorems/b25a6752-fc46-4a90-9968-e8a4df497fb4
-- title:
--   T: amin T ret
-- statement:
--   The T construction uses the amin T ret property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L108-L112
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L108-L112

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_Timed_MinPath
set_option autoImplicit true
open ULHC ULHC.T
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edgeT : α → α → TimeM Bool) (w : α → ℕ)

theorem ULHC.T.aminT_ret {γ β : Type} (f : γ → TimeM (Option (ℕ × β))) : ∀ l : List γ,
    (aminT f l).ret = MP.amin (fun y => (f y).ret) l
  := by sorry
