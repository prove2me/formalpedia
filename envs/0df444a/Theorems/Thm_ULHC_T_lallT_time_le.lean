-- Prove2me | Theorems.Thm_ULHC_T_lallT_time_le
-- name    : ULHC.T.lallT_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:31:01.416828+00:00
-- url     : https://prove2.me/theorems/2e2e33c2-2bf7-41f2-a563-fdd2bb6395b9
-- title:
--   T: lall T time le
-- statement:
--   The T construction uses the lall T time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/TimeM.lean#L184-L186
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/TimeM.lean#L184-L186

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM
set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}

theorem ULHC.T.lallT_time_le (p : α → TimeM Bool) (l : List α) (c : ℕ) (h : ∀ x ∈ l, (p x).time ≤ c) :
    (lallT p l).time ≤ l.length * (c + 1) := by sorry
