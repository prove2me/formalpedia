-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_nextIn_le
-- name    : OrdinalStepUp.ErdosRado.nextIn_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:54.488495+00:00
-- url     : https://prove2.me/theorems/2d3dad41-36f2-4f20-b0d7-b8ea5906ddd0
-- title:
--   Erdos Rado: next In le
-- statement:
--   Nothing of `𝒜` sits strictly between `x` and `nextIn wo 𝒜 x`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L646-L653
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L646-L653

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}

theorem OrdinalStepUp.ErdosRado.nextIn_le {x : wo.α} {𝒜 : Set wo.α} (h : ∃ y, y ∈ 𝒜 ∧ wo.r x y) {z : wo.α} (hz : z ∈ 𝒜)
    (hxz : wo.r x z) :
    nextIn 𝒜 x = z ∨ wo.r (nextIn 𝒜 x) z := by sorry
