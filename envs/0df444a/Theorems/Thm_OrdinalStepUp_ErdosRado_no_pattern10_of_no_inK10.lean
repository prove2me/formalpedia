-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_no_pattern10_of_no_inK10
-- name    : OrdinalStepUp.ErdosRado.no_pattern10_of_no_inK10
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:49:22.710387+00:00
-- url     : https://prove2.me/theorems/9b8a8515-49fe-4f59-9317-b9c5c2cba852
-- title:
--   Erdos Rado: no pattern10 of no in K10
-- statement:
--   Lemma 4.16's hypothesis (ii), from `[𝒜]ⁿ⁺⁴ ∩ K(1,0) = ∅`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1100-L1107
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1100-L1107

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

theorem OrdinalStepUp.ErdosRado.no_pattern10_of_no_inK10 (hA : IsIndec (otp 𝒜))
    (h : ∀ u : FinChain (n + 4), (∀ i, u i ∈ 𝒜) → ¬ InK10 u) :
    ¬ ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, a ≺w b ∧ b ≺w c ∧ ¬ a ≺ b ∧ b ≺ c := by sorry
