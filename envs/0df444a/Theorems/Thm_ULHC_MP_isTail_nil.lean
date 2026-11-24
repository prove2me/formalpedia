-- Prove2me | Theorems.Thm_ULHC_MP_isTail_nil
-- name    : ULHC.MP.isTail_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:58:14.226068+00:00
-- url     : https://prove2.me/theorems/5120e025-bd29-44d6-b1c9-9d61ba055ec0
-- title:
--   MP: is Tail nil
-- statement:
--   The MP construction uses the is Tail nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L98-L98
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L98-L98

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}

theorem ULHC.MP.isTail_nil {x : α} : IsTail mid tgt edge x [] ↔ tgt x = true := by sorry
