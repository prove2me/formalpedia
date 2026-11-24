-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_wo_nextIn
-- name    : OrdinalStepUp.ErdosRado.wo_nextIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:47:28.6683+00:00
-- url     : https://prove2.me/theorems/d86f323e-b84a-40fb-a5d9-353a0a30a023
-- title:
--   Erdos Rado: wo next In
-- statement:
--   The Erdos Rado construction uses the wo next In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L642-L643
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L642-L643

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

theorem OrdinalStepUp.ErdosRado.wo_nextIn {x : wo.α} {𝒜 : Set wo.α} (h : ∃ y, y ∈ 𝒜 ∧ wo.r x y) : wo.r x (nextIn 𝒜 x) := by sorry
