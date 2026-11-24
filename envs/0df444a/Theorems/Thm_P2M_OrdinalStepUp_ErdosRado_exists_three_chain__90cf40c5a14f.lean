-- Prove2me | Theorems.Thm_P2M_OrdinalStepUp_ErdosRado_exists_three_chain__90cf40c5a14f
-- name    : P2M_OrdinalStepUp_ErdosRado_exists_three_chain__90cf40c5a14f
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:48:39.075751+00:00
-- url     : https://prove2.me/theorems/1baf8458-6a04-4998-a51f-d48e4e97151e
-- title:
--   P2 M Ordinal Step Up Erdos Rado exists three chain  90cf40c5a14f: P2 M Ordinal Step Up Erdos Rado exists three chain  90cf40c5a14f
-- statement:
--   The mirror of `exists_three_chain`: a three-chain with `P` failing on the
--   first pair and holding on the second.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L413-L419
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L413-L419

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

theorem P2M_OrdinalStepUp_ErdosRado_exists_three_chain__90cf40c5a14f
    (P : wo.α → wo.α → Prop) {𝒜 : Set wo.α} (hA : IsIndec (otpOf wo 𝒜))
    (hD : ∀ ℬ, ℬ ⊆ 𝒜 → otpOf wo ℬ = otpOf wo 𝒜 →
      ¬ ((∀ u ∈ ℬ, ∀ v ∈ ℬ, wo.r u v → P u v) ∨ (∀ u ∈ ℬ, ∀ v ∈ ℬ, wo.r u v → ¬ P u v))) :
    ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, wo.r a b ∧ wo.r b c ∧ ¬ P a b ∧ P b c := by sorry

alias «OrdinalStepUp».«ErdosRado».«exists_three_chain'» := P2M_OrdinalStepUp_ErdosRado_exists_three_chain__90cf40c5a14f
