-- Prove2me | Theorems.Thm_ULHC_MP_stepCost_le
-- name    : ULHC.MP.stepCost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:28.785656+00:00
-- url     : https://prove2.me/theorems/ed5efd5d-11f2-4d87-8b96-fc0769ce6c06
-- title:
--   MP: step Cost le
-- statement:
--   The MP construction uses the step Cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostMinPath.lean#L71-L77
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostMinPath.lean#L71-L77

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

theorem ULHC.MP.stepCost_le (tbl : List (α × Option (ℕ × List α))) (ht : tbl.length ≤ NL.length)
    {x : α} (hx : x ∈ NL) :
    stepCost NL mid tgt ec tbl x ≤ NL.length * (E + NL.length + 5) + 3 := by sorry
