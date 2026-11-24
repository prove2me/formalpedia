-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_up_forces_up_of_no_inP01
-- name    : OrdinalStepUp.ErdosRado.up_forces_up_of_no_inP01
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:49:24.090909+00:00
-- url     : https://prove2.me/theorems/0fb65400-42e1-4ae9-843b-6c0c27c37ef6
-- title:
--   Erdos Rado: up forces up of no in P01
-- statement:
--   Lemma 4.17's hypothesis (i), from `[𝒜]ⁿ⁺⁴ ∩ P(0,1) = ∅`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1110-L1121
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1110-L1121

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

theorem OrdinalStepUp.ErdosRado.up_forces_up_of_no_inP01 (hA : IsIndec (otp 𝒜))
    (hom : HomAgree 𝒜)
    (h : ∀ u : FinChain (n + 4), (∀ i, u i ∈ 𝒜) → ¬ InP01 u) :
    ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, a ≺w b → b ≺w c → c ≺w e →
      disc a b < disc b c → disc b c < disc c e := by sorry
