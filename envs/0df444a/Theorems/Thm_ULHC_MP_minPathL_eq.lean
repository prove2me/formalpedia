-- Prove2me | Theorems.Thm_ULHC_MP_minPathL_eq
-- name    : ULHC.MP.minPathL_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:27.195605+00:00
-- url     : https://prove2.me/theorems/f659bf5e-3e2f-4b53-be28-6aaca8441d67
-- title:
--   MP: min Path L eq
-- statement:
--   The MP construction uses the min Path L eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L337-L339
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L337-L339

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)

theorem ULHC.MP.minPathL_eq :
    minPathL NL src mid tgt edge w = (amin (srcF NL src mid tgt edge w) NL).map Prod.snd := by sorry
