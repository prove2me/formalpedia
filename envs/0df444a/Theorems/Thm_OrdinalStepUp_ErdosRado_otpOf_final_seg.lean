-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_otpOf_final_seg
-- name    : OrdinalStepUp.ErdosRado.otpOf_final_seg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:47:50.136625+00:00
-- url     : https://prove2.me/theorems/ddff80f0-d096-4b25-9cfc-a241ca0d472f
-- title:
--   Erdos Rado: otp Of final seg
-- statement:
--   Lemma 4.15. A final segment of a set of order type `θ` has order type
--   `θ` again, provided the part it omits is short.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L356-L364
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L356-L364

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

theorem OrdinalStepUp.ErdosRado.otpOf_final_seg
    {𝒜 ℬ : Set _} (hA : IsIndec (otpOf wo 𝒜)) (hBA : ℬ ⊆ 𝒜)
    (hfinal : ∀ y ∈ ℬ, ∀ x ∈ 𝒜, wo.r y x → x ∈ ℬ)
    (hsmall : otpOf wo (𝒜 \ ℬ) < otpOf wo 𝒜) :
    otpOf wo ℬ = otpOf wo 𝒜 := by sorry
