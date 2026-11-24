-- Prove2me | Theorems.Thm_ULHC_MP_sum_map_le
-- name    : ULHC.MP.sum_map_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:41.124349+00:00
-- url     : https://prove2.me/theorems/e76b32f2-a6ed-4b58-bef5-06cc56eb9721
-- title:
--   MP: sum map le
-- statement:
--   The MP construction uses the sum map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostMinPath.lean#L53-L61
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostMinPath.lean#L53-L61

import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_CostMinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type} [DecidableEq α]

theorem ULHC.MP.sum_map_le {γ : Type} (l : List γ) (f : γ → ℕ) (b : ℕ) (h : ∀ x ∈ l, f x ≤ b) :
    (l.map f).sum ≤ l.length * b := by sorry
