-- Prove2me | Theorems.Thm_ULHC_T_lsum_le
-- name    : ULHC.T.lsum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:17:32.438869+00:00
-- url     : https://prove2.me/theorems/06a316b9-8393-4737-909f-6423835c72cb
-- title:
--   T: lsum le
-- statement:
--   The T construction uses the lsum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/TimeM.lean#L161-L169
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/TimeM.lean#L161-L169

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_Timed_TimeM
set_option autoImplicit true
open ULHC ULHC.T
open Finset
variable {α β : Type}

theorem ULHC.T.lsum_le {γ : Type} (l : List γ) (g : γ → ℕ) (c : ℕ) (h : ∀ x ∈ l, g x ≤ c) :
    (l.map g).sum ≤ l.length * c := by sorry
