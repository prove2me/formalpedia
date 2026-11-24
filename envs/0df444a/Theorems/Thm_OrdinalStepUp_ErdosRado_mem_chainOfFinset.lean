-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_mem_chainOfFinset
-- name    : OrdinalStepUp.ErdosRado.mem_chainOfFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:09.980956+00:00
-- url     : https://prove2.me/theorems/1747804f-3c4a-47b9-a58b-956b278353d2
-- title:
--   Erdos Rado: mem chain Of Finset
-- statement:
--   The Erdos Rado construction uses the mem chain Of Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L805-L808
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L805-L808

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

theorem OrdinalStepUp.ErdosRado.mem_chainOfFinset (𝒯 : Finset SetOrd) (hT : 𝒯.card = n) (i : Fin n) :
    (chainOfFinset 𝒯 hT) i ∈ 𝒯 := by sorry
