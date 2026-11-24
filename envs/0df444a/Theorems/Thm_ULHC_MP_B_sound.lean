-- Prove2me | Theorems.Thm_ULHC_MP_B_sound
-- name    : ULHC.MP.B_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:00.987744+00:00
-- url     : https://prove2.me/theorems/12b8939f-d40b-4bb2-a70f-da9f3f866173
-- title:
--   MP: B sound
-- statement:
--   The MP construction uses the B sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L352-L402
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L352-L402

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)

theorem ULHC.MP.B_sound : ∀ (k : ℕ) (x : α) (r : ℕ × List α), B NL mid tgt edge w k x = some r →
    r.1 = pw w r.2 ∧ ∃ L, r.2 = x :: L ∧ IsTail mid tgt edge x L ∧
      (∀ z ∈ r.2, z ∈ NL) ∧ L.length < k := by sorry
