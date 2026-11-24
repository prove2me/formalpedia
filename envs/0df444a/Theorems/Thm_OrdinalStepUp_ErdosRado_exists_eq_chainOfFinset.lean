-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_exists_eq_chainOfFinset
-- name    : OrdinalStepUp.ErdosRado.exists_eq_chainOfFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:57.265609+00:00
-- url     : https://prove2.me/theorems/7119555b-fca8-40fa-8ea6-5bc263c486ec
-- title:
--   Erdos Rado: exists eq chain Of Finset
-- statement:
--   Every point of `T` is hit by its enumeration.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L811-L814
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L811-L814

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

theorem OrdinalStepUp.ErdosRado.exists_eq_chainOfFinset (𝒯 : Finset SetOrd) (hT : 𝒯.card = n)
    (ha : a ∈ 𝒯) : ∃ i, (chainOfFinset 𝒯 hT) i = a := by sorry
