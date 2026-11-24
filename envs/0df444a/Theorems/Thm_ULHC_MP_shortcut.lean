-- Prove2me | Theorems.Thm_ULHC_MP_shortcut
-- name    : ULHC.MP.shortcut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:53:56.356797+00:00
-- url     : https://prove2.me/theorems/f7b39215-3458-43e8-b4d9-fc4edd5138b6
-- title:
--   MP: shortcut
-- statement:
--   The MP construction uses the shortcut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L153-L167
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L153-L167

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}

theorem ULHC.MP.shortcut {x : α} {L : List α} (h : IsTail mid tgt edge x L) :
    ∃ L', IsTail mid tgt edge x L' ∧ (x :: L').Nodup ∧ (x :: L').Sublist (x :: L) := by sorry
