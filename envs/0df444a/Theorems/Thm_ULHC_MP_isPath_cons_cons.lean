-- Prove2me | Theorems.Thm_ULHC_MP_isPath_cons_cons
-- name    : ULHC.MP.isPath_cons_cons
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:11:37.741523+00:00
-- url     : https://prove2.me/theorems/8b1aa5ca-989a-4468-b345-b463e45f52de
-- title:
--   MP: is Path cons cons
-- statement:
--   The MP construction uses the is Path cons cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L110-L112
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L110-L112

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}

theorem ULHC.MP.isPath_cons_cons {x y : α} {L : List α} :
    IsPath src mid tgt edge (x :: y :: L) ↔
      src x = true ∧ mid x = true ∧ edge x y = true ∧ IsTail mid tgt edge y L := by sorry
