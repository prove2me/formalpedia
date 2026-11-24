-- Prove2me | Theorems.Thm_ULHC_MP_minPathL_min
-- name    : ULHC.MP.minPathL_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:19.782441+00:00
-- url     : https://prove2.me/theorems/6a1a4ab0-6fc8-4963-9e46-bf4a4bffdb5b
-- title:
--   MP: min Path L min
-- statement:
--   The MP construction uses the min Path L min property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L498-L505
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/MinPath.lean#L498-L505

import Mathlib
import Definitions.Def_ULHC_MinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type}
variable [DecidableEq α]
variable (NL : List α) (src mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)

theorem ULHC.MP.minPathL_min {p : List α} (h : minPathL NL src mid tgt edge w = some p)
    (q : List α) (hq : IsPath src mid tgt edge q) (hqN : ∀ x ∈ q, x ∈ NL) :
    pw w p ≤ pw w q := by sorry
