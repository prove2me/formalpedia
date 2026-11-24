-- Prove2me | Theorems.Thm_ULHC_MP_isPath_singleton
-- name    : ULHC.MP.isPath_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:20.000804+00:00
-- url     : https://prove2.me/theorems/27d88114-5b5b-4426-a469-8f24adfeba6c
-- title:
--   MP: is Path singleton
-- statement:
--   The MP construction uses the is Path singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L107-L108
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L107-L108

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable {src mid tgt : α → Bool} {edge : α → α → Bool} {w : α → ℕ}

theorem ULHC.MP.isPath_singleton {x : α} :
    IsPath src mid tgt edge [x] ↔ src x = true ∧ tgt x = true := by sorry
