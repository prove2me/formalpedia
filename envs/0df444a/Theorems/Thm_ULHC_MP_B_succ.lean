-- Prove2me | Theorems.Thm_ULHC_MP_B_succ
-- name    : ULHC.MP.B_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:54:15.476317+00:00
-- url     : https://prove2.me/theorems/581a6f9e-8e22-460f-8864-f09d2c830a47
-- title:
--   MP: B succ
-- statement:
--   The MP construction uses the B succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L343-L347
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L343-L347

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)

theorem ULHC.MP.B_succ (k : ℕ) (x : α) :
    B NL mid tgt edge w (k + 1) x =
      if x ∈ NL then step NL mid tgt edge w (B NL mid tgt edge w k) x else none := by sorry
