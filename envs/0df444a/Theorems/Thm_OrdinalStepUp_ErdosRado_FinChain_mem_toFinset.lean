-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_FinChain_mem_toFinset
-- name    : OrdinalStepUp.ErdosRado.FinChain.mem_toFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:47:28.27653+00:00
-- url     : https://prove2.me/theorems/4418d3b0-53b6-46c1-a807-d5157eb4f46e
-- title:
--   Fin Chain: mem to Finset
-- statement:
--   The Fin Chain construction uses the mem to Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L821-L823
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L821-L823

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

theorem OrdinalStepUp.ErdosRado.FinChain.mem_toFinset (u : FinChain n) {x : SetOrd} :
    x ∈ u.toFinset ↔ ∃ i, u i = x := by sorry
