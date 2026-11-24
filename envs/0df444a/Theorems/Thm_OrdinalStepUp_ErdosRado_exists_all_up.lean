-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_exists_all_up
-- name    : OrdinalStepUp.ErdosRado.exists_all_up
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:48:41.218656+00:00
-- url     : https://prove2.me/theorems/f49121aa-b5eb-47dd-92ef-64bfb0fc057f
-- title:
--   Erdos Rado: exists all up
-- statement:
--   Lemma 4.17, with the discrepancy abstracted to an arbitrary `d`.
--
--   The two hypotheses are [dG21]'s (i) and (ii): `[𝒜]ʳ ∩ P(0,1) = ∅` says no
--   four-chain has its discrepancy go up then down, which -- since `hne` rules out
--   ties -- is the implication "up forces up again"; (ii) is the mirror.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L540-L580
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L540-L580

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

theorem OrdinalStepUp.ErdosRado.exists_all_up
    (d : wo.α → wo.α → Ordinal) {𝒜 : Set _} (hA : IsIndec (otpOf wo 𝒜))
    (hne : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, wo.r a b → wo.r b c → d a b ≠ d b c)
    (h : (∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, wo.r a b → wo.r b c → wo.r c e →
            d a b < d b c → d b c < d c e) ∨
         (∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, wo.r a b → wo.r b c → wo.r c e →
            d b c < d a b → d c e < d b c)) :
    ∃ ℬ ⊆ 𝒜, otpOf wo ℬ = otpOf wo 𝒜 ∧
      ∀ a ∈ ℬ, ∀ b ∈ ℬ, ∀ c ∈ ℬ, wo.r a b → wo.r b c → d a b < d b c := by sorry
