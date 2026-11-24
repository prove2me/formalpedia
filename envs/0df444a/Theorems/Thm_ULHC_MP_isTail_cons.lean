-- Prove2me | Theorems.Thm_ULHC_MP_isTail_cons
-- name    : ULHC.MP.isTail_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:53:19.350228+00:00
-- url     : https://prove2.me/theorems/751e56b4-9f55-4848-a0da-46692a1f0ac7
-- title:
--   MP: is Tail cons
-- statement:
--   The MP construction uses the is Tail cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L100-L102
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L100-L102

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}

theorem ULHC.MP.isTail_cons {x y : α} {L : List α} :
    IsTail mid tgt edge x (y :: L) ↔
      mid x = true ∧ edge x y = true ∧ IsTail mid tgt edge y L := by sorry
