-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_not_inP10_of_inP0
-- name    : OrdinalStepUp.ErdosRado.not_inP10_of_inP0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:49:10.278219+00:00
-- url     : https://prove2.me/theorems/25a6c446-8686-419f-bcad-5bc758830067
-- title:
--   Erdos Rado: not in P10 of in P0
-- statement:
--   `P₀` is disjoint from `P(1,0)` for the same reason, one step earlier.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1002-L1003
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1002-L1003

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

theorem OrdinalStepUp.ErdosRado.not_inP10_of_inP0 {u : FinChain (n + 4)} (h : InP0 u) : ¬ InP10 u := by sorry
