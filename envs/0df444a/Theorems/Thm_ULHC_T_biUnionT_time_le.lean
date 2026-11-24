-- Prove2me | Theorems.Thm_ULHC_T_biUnionT_time_le
-- name    : ULHC.T.biUnionT_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:27:47.806223+00:00
-- url     : https://prove2.me/theorems/f8a7e7b8-baf0-425d-b8ec-6126535b19ba
-- title:
--   T: bi Union T time le
-- statement:
--   The T construction uses the bi Union T time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/TimeM.lean#L204-L207
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/TimeM.lean#L204-L207

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM
set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}

theorem ULHC.T.biUnionT_time_le [DecidableEq β] (f : α → TimeM (Finset β)) (s : Finset α) (c d : ℕ)
    (h : ∀ x ∈ s, (f x).time ≤ c) (hd : ∀ x ∈ s, (f x).ret.card ≤ d) :
    (biUnionT f s).time ≤ s.card * (c + d + 1) := by sorry
