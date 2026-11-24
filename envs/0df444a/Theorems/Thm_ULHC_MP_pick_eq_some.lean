-- Prove2me | Theorems.Thm_ULHC_MP_pick_eq_some
-- name    : ULHC.MP.pick_eq_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:58:49.402465+00:00
-- url     : https://prove2.me/theorems/71fdbb78-0851-4b0f-bf45-a1f6b4dd7a34
-- title:
--   MP: pick eq some
-- statement:
--   The MP construction uses the pick eq some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L198-L209
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L198-L209

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {γ β : Type}

theorem ULHC.MP.pick_eq_some {a b : Option (ℕ × β)} {r : ℕ × β} (h : pick a b = some r) :
    a = some r ∨ b = some r := by sorry
