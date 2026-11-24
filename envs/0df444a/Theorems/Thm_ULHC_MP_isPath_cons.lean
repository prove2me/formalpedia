-- Prove2me | Theorems.Thm_ULHC_MP_isPath_cons
-- name    : ULHC.MP.isPath_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:36:25.120449+00:00
-- url     : https://prove2.me/theorems/c48e39e3-8644-4ef3-9595-727d86201b99
-- title:
--   MP: is Path cons
-- statement:
--   The MP construction uses the is Path cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L104-L105
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L104-L105

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}

theorem ULHC.MP.isPath_cons {x : α} {L : List α} :
    IsPath src mid tgt edge (x :: L) ↔ src x = true ∧ IsTail mid tgt edge x L := by sorry
