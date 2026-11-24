-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_no_pattern01_of_no_inK01
-- name    : OrdinalStepUp.ErdosRado.no_pattern01_of_no_inK01
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:49:23.037307+00:00
-- url     : https://prove2.me/theorems/6c7cce4f-c7b0-4bc1-9848-1d193160bf80
-- title:
--   Erdos Rado: no pattern01 of no in K01
-- statement:
--   Lemma 4.16's hypothesis (i), from `[𝒜]ⁿ⁺⁴ ∩ K(0,1) = ∅`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1090-L1097
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1090-L1097

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

theorem OrdinalStepUp.ErdosRado.no_pattern01_of_no_inK01 (hA : IsIndec (otp 𝒜))
    (h : ∀ u : FinChain (n + 4), (∀ i, u i ∈ 𝒜) → ¬ InK01 u) :
    ¬ ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, a ≺w b ∧ b ≺w c ∧ a ≺ b ∧ ¬ b ≺ c := by sorry
