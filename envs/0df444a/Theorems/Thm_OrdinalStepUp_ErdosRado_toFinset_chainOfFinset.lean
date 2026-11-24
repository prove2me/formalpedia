-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_toFinset_chainOfFinset
-- name    : OrdinalStepUp.ErdosRado.toFinset_chainOfFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:47:25.534325+00:00
-- url     : https://prove2.me/theorems/224ba925-74f5-47fb-bbf4-26d2bdc45353
-- title:
--   Erdos Rado: to Finset chain Of Finset
-- statement:
--   Sorting a finite set and then forgetting the order gives it back.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L830-L834
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L830-L834

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

theorem OrdinalStepUp.ErdosRado.toFinset_chainOfFinset (𝒯 : Finset SetOrd) (hT : 𝒯.card = n) :
    (chainOfFinset 𝒯 hT).toFinset = 𝒯 := by sorry
