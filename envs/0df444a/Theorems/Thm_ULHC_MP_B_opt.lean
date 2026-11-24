-- Prove2me | Theorems.Thm_ULHC_MP_B_opt
-- name    : ULHC.MP.B_opt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:08.114882+00:00
-- url     : https://prove2.me/theorems/8d8fbe58-969b-4050-b695-59941eeb1912
-- title:
--   MP: B opt
-- statement:
--   The MP construction uses the B opt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L407-L448
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L407-L448

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)

theorem ULHC.MP.B_opt : ∀ (k : ℕ) (x : α) (L : List α), IsTail mid tgt edge x L →
    (∀ z ∈ x :: L, z ∈ NL) → L.length < k →
      ∃ r, B NL mid tgt edge w k x = some r ∧ r.1 ≤ pw w (x :: L) := by sorry
