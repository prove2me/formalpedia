-- Prove2me | Theorems.Thm_ULHC_T_lsum_mono
-- name    : ULHC.T.lsum_mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:24:59.920273+00:00
-- url     : https://prove2.me/theorems/3dee85e0-0386-4e95-a27d-86f915f4992e
-- title:
--   T: lsum mono
-- statement:
--   The T construction uses the lsum mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L155-L161
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Timed/MinPath.lean#L155-L161

import Definitions.Def_ULHC_Timed_TimeM
import Definitions.Def_ULHC_CostMinPath
import Definitions.Def_ULHC_Timed_MinPath
set_option autoImplicit true
open ULHC ULHC.T
variable {α : Type} [DecidableEq α]

theorem ULHC.T.lsum_mono {γ : Type} (l : List γ) (f g : γ → ℕ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by sorry
