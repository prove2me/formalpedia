-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_not_inP10_of_inP01
-- name    : OrdinalStepUp.ErdosRado.not_inP10_of_inP01
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:49:10.536964+00:00
-- url     : https://prove2.me/theorems/ba789aae-7b8b-4db8-a74e-92a12f43f9c8
-- title:
--   Erdos Rado: not in P10 of in P01
-- statement:
--   `P(0,1)` and `P(1,0)` are disjoint from each other.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1006-L1007
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1006-L1007

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

theorem OrdinalStepUp.ErdosRado.not_inP10_of_inP01 {u : FinChain (n + 4)} (h : InP01 u) : ¬ InP10 u := by sorry
