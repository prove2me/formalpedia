-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_exists_three_chain
-- name    : OrdinalStepUp.ErdosRado.exists_three_chain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:47:52.343811+00:00
-- url     : https://prove2.me/theorems/4e75ec1c-775b-445a-a565-73ff66f69473
-- title:
--   Erdos Rado: exists three chain
-- statement:
--   If no subset of `𝒜` of full order type is
--   `P`-homogeneous, then some three-chain in `𝒜` has `P` on its first pair and not
--   on its second.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L391-L409
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L391-L409

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

theorem OrdinalStepUp.ErdosRado.exists_three_chain
    (P : wo.α → wo.α → Prop) {𝒜 : Set wo.α} (hA : IsIndec (otpOf wo 𝒜))
    (hD : ∀ ℬ, ℬ ⊆ 𝒜 → otpOf wo ℬ = otpOf wo 𝒜 →
      ¬ ((∀ u ∈ ℬ, ∀ v ∈ ℬ, wo.r u v → P u v) ∨ (∀ u ∈ ℬ, ∀ v ∈ ℬ, wo.r u v → ¬ P u v))) :
    ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, wo.r a b ∧ wo.r b c ∧ P a b ∧ ¬ P b c := by sorry
