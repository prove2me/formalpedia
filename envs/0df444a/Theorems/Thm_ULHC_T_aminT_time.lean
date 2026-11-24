-- Prove2me | Theorems.Thm_ULHC_T_aminT_time
-- name    : ULHC.T.aminT_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:40:18.652651+00:00
-- url     : https://prove2.me/theorems/5f45f0e9-cf40-42bc-83fd-4cdf191087d9
-- title:
--   T: amin T time
-- statement:
--   The T construction uses the amin T time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L171-L176
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L171-L176

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_Timed_MinPath
set_option autoImplicit true
open ULHC ULHC.T
variable {α : Type} [DecidableEq α]

theorem ULHC.T.aminT_time {γ β : Type} (f : γ → TimeM (Option (ℕ × β))) : ∀ l : List γ,
    (aminT f l).time = (l.map fun y => (f y).time + 1).sum + 1
  := by sorry
