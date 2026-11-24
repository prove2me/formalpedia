-- Prove2me | Theorems.Thm_ULHC_MP_nextCost_le
-- name    : ULHC.MP.nextCost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:39.736674+00:00
-- url     : https://prove2.me/theorems/62891c90-027e-4a24-b42e-4c48a66a23a6
-- title:
--   MP: next Cost le
-- statement:
--   The MP construction uses the next Cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostMinPath.lean#L81-L84
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostMinPath.lean#L81-L84

import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_CostMinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
  (ec : α → α → ℕ) (sc : α → ℕ) {E S : ℕ}
  (hE : ∀ x ∈ NL, ∀ y ∈ NL, ec x y ≤ E) (hS : ∀ x ∈ NL, sc x ≤ S)
include hE
omit [DecidableEq α]

theorem ULHC.MP.nextCost_le (tbl : List (α × Option (ℕ × List α))) (ht : tbl.length ≤ NL.length) :
    nextCost NL mid tgt ec tbl ≤ NL.length * (NL.length * (E + NL.length + 5) + 4) := by sorry
