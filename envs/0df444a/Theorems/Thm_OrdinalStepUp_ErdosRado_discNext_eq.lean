-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_discNext_eq
-- name    : OrdinalStepUp.ErdosRado.discNext_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:47:56.952297+00:00
-- url     : https://prove2.me/theorems/cf1aeb2a-6ccf-4fcf-8807-9d7ce54c17cd
-- title:
--   Erdos Rado: disc Next eq
-- statement:
--   On a `P₀`-homogeneous set the next-point discrepancy is the discrepancy to
--   *any* later point of the set. This is the step [dG21]
--   takes with Observation 4.2 after checking `δ_{ξᵢ} < δ(h_{ξᵢ+1}, h_{ξᵢ₊₁})`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L670-L677
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L670-L677

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

theorem OrdinalStepUp.ErdosRado.discNext_eq
    (hup : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c)
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hab : a ≺w b) :
    discNext 𝒜 a = disc a b := by sorry
