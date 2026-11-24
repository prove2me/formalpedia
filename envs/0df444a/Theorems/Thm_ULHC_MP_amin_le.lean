-- Prove2me | Theorems.Thm_ULHC_MP_amin_le
-- name    : ULHC.MP.amin_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:53:59.668643+00:00
-- url     : https://prove2.me/theorems/5fe2b4eb-0439-4300-b066-941239c925eb
-- title:
--   MP: amin le
-- statement:
--   The MP construction uses the amin le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L244-L254
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L244-L254

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {γ β : Type}

theorem ULHC.MP.amin_le {f : γ → Option (ℕ × β)} {l : List γ} {y : γ} {r : ℕ × β}
    (hy : y ∈ l) (h : f y = some r) : ∃ r', amin f l = some r' ∧ r'.1 ≤ r.1 := by sorry
