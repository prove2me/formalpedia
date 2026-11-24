-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_exists_all_disc_up
-- name    : OrdinalStepUp.ErdosRado.exists_all_disc_up
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:48:42.587802+00:00
-- url     : https://prove2.me/theorems/788d7eb4-7e8d-45e4-9936-201a7e16d2e8
-- title:
--   Erdos Rado: exists all disc up
-- statement:
--   Lemma 4.17 for the actual discrepancy.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L583-L591
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L583-L591

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

theorem OrdinalStepUp.ErdosRado.exists_all_disc_up (hA : IsIndec (otp 𝒜)) (hom : HomAgree 𝒜)
    (h : (∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, a ≺w b → b ≺w c → c ≺w e →
            disc a b < disc b c → disc b c < disc c e) ∨
         (∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, a ≺w b → b ≺w c → c ≺w e →
            disc b c < disc a b → disc c e < disc b c)) :
    ∃ ℬ ⊆ 𝒜, otp ℬ = otp 𝒜 ∧
      ∀ a ∈ ℬ, ∀ b ∈ ℬ, ∀ c ∈ ℬ, a ≺w b → b ≺w c → disc a b < disc b c := by sorry
