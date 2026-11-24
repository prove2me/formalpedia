-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_otpOf_initial_lt
-- name    : OrdinalStepUp.ErdosRado.otpOf_initial_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:37.061684+00:00
-- url     : https://prove2.me/theorems/d7795af9-18d2-4be7-9d79-a04336e24269
-- title:
--   Erdos Rado: otp Of initial lt
-- statement:
--   The part of `𝒜` strictly below a point of `𝒜` is one of the initial
--   segments of `𝒜`'s own well-order, hence has strictly smaller order type. This
--   is what makes the smallness hypothesis of `otpOf_final_seg` automatic.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L369-L376
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L369-L376

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

theorem OrdinalStepUp.ErdosRado.otpOf_initial_lt {𝒜 : Set _} {x₀ : wo.α} (hx₀ : x₀ ∈ 𝒜) :
    otpOf wo {y ∈ 𝒜 | wo.r y x₀} < otpOf wo 𝒜 := by sorry
