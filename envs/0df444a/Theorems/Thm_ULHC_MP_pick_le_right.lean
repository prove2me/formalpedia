-- Prove2me | Theorems.Thm_ULHC_MP_pick_le_right
-- name    : ULHC.MP.pick_le_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:58:54.566227+00:00
-- url     : https://prove2.me/theorems/d4a3001c-c244-4ba3-86c3-9992ef9b33d2
-- title:
--   MP: pick le right
-- statement:
--   The MP construction uses the pick le right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L220-L227
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L220-L227

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {γ β : Type}

theorem ULHC.MP.pick_le_right {a b : Option (ℕ × β)} {r : ℕ × β} (h : b = some r) :
    ∃ r', pick a b = some r' ∧ r'.1 ≤ r.1 := by sorry
