-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_nextIn_mem
-- name    : OrdinalStepUp.ErdosRado.nextIn_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:47:28.71465+00:00
-- url     : https://prove2.me/theorems/81910f06-9506-4418-8e3b-d0758519b521
-- title:
--   Erdos Rado: next In mem
-- statement:
--   The Erdos Rado construction uses the next In mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L639-L640
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L639-L640

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

theorem OrdinalStepUp.ErdosRado.nextIn_mem {x : wo.α} {𝒜 : Set wo.α} (h : ∃ y, y ∈ 𝒜 ∧ wo.r x y) : nextIn 𝒜 x ∈ 𝒜 := by sorry
