-- Prove2me | Theorems.Thm_P2M_ULHC_MP_lsum_mono__0cdf42948454
-- name    : P2M_ULHC_MP_lsum_mono__0cdf42948454
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:48.657398+00:00
-- url     : https://prove2.me/theorems/27b5ce2d-0d00-4404-8545-07de520b8106
-- title:
--   P2 M ULHC MP lsum mono  0cdf42948454: P2 M ULHC MP lsum mono  0cdf42948454
-- statement:
--   The P2 M ULHC MP lsum mono  0cdf42948454 construction uses the P2 M ULHC MP lsum mono  0cdf42948454 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostMinPath.lean#L120-L124
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CostMinPath.lean#L120-L124

import Definitions.Def_ULHC_MinPath
import Definitions.Def_ULHC_CostMinPath
set_option autoImplicit true
open ULHC ULHC.MP
variable {α : Type} [DecidableEq α]
variable (NL : List α) (mid tgt : α → Bool) (edge : α → α → Bool) (w : α → ℕ)
  {ec ec' : α → α → ℕ} {sc sc' : α → ℕ} (hE : ∀ x y, ec x y ≤ ec' x y) (hS : ∀ x, sc x ≤ sc' x)

theorem P2M_ULHC_MP_lsum_mono__0cdf42948454 {γ : Type} (l : List γ) (f g : γ → ℕ) (h : ∀ x, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by sorry

alias «ULHC».«MP».«lsum_mono'» := P2M_ULHC_MP_lsum_mono__0cdf42948454
