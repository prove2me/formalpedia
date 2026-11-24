-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_not_all_down
-- name    : OrdinalStepUp.ErdosRado.not_all_down
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:39.047162+00:00
-- url     : https://prove2.me/theorems/f8c02cba-77bf-4a7f-941f-06933aa46759
-- title:
--   Erdos Rado: not all down
-- statement:
--   No set of full order type has its discrepancy going *down* across every
--   triple.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L524-L533
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L524-L533

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

theorem OrdinalStepUp.ErdosRado.not_all_down
    (d : wo.α → wo.α → Ordinal) {𝒞 : Set _} (hC : IsIndec (otpOf wo 𝒞))
    (hdown : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, ∀ c ∈ 𝒞, wo.r a b → wo.r b c → d b c < d a b) : False := by sorry
