-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_inK1_of_allDisagree
-- name    : OrdinalStepUp.ErdosRado.inK1_of_allDisagree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:49:18.081182+00:00
-- url     : https://prove2.me/theorems/0bdd69e1-a726-4089-b1f9-1403ffb85879
-- title:
--   Erdos Rado: in K1 of all Disagree
-- statement:
--   On an all-disagreeing set every chain lies in `K₁`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1026-L1029
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1026-L1029

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

theorem OrdinalStepUp.ErdosRado.inK1_of_allDisagree (h : AllDisagree ℬ)
    {u : FinChain (n + 1)} (hu : ∀ i, u i ∈ ℬ) : InK1 u := by sorry
