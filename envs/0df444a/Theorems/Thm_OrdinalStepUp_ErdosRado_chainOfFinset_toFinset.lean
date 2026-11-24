-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_chainOfFinset_toFinset
-- name    : OrdinalStepUp.ErdosRado.chainOfFinset_toFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:49:27.611798+00:00
-- url     : https://prove2.me/theorems/9c3c363e-4b4c-4de2-800d-294dc2f8cda0
-- title:
--   Erdos Rado: chain Of Finset to Finset
-- statement:
--   A chain is recovered from its own finite set: the increasing enumeration
--   is unique. Both lists are `WOle`-sorted and permutations of one another, and
--   `WOle` is antisymmetric, so they are equal.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1151-L1161
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1151-L1161

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

theorem OrdinalStepUp.ErdosRado.chainOfFinset_toFinset (u : FinChain n) :
    chainOfFinset u.toFinset u.card_toFinset = u := by sorry
