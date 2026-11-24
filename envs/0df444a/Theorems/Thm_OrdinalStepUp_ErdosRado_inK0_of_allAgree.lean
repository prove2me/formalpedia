-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_inK0_of_allAgree
-- name    : OrdinalStepUp.ErdosRado.inK0_of_allAgree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:49:14.965577+00:00
-- url     : https://prove2.me/theorems/ae8ddbbe-3fb2-4c24-975f-b5384bb732d8
-- title:
--   Erdos Rado: in K0 of all Agree
-- statement:
--   On an all-agreeing set every chain lies in `K₀`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1020-L1023
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1020-L1023

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

theorem OrdinalStepUp.ErdosRado.inK0_of_allAgree (h : AllAgree ℬ)
    {u : FinChain (n + 1)} (hu : ∀ i, u i ∈ ℬ) : InK0 u := by sorry
