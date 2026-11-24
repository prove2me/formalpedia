-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_not_inP01_of_inP0
-- name    : OrdinalStepUp.ErdosRado.not_inP01_of_inP0
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:49:12.815561+00:00
-- url     : https://prove2.me/theorems/93875865-cb49-471a-a811-68482eb335d2
-- title:
--   Erdos Rado: not in P01 of in P0
-- statement:
--   `P₀` is disjoint from `P(0,1)`: an all-rising sequence never falls.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L998-L999
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L998-L999

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

theorem OrdinalStepUp.ErdosRado.not_inP01_of_inP0 {u : FinChain (n + 4)} (h : InP0 u) : ¬ InP01 u := by sorry
