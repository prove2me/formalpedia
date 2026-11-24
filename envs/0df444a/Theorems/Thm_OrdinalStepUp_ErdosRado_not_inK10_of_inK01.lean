-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_not_inK10_of_inK01
-- name    : OrdinalStepUp.ErdosRado.not_inK10_of_inK01
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:49:16.000804+00:00
-- url     : https://prove2.me/theorems/54e6f72a-680f-4d3e-9501-ba8a8ef0aeb1
-- title:
--   Erdos Rado: not in K10 of in K01
-- statement:
--   `K(0,1)` and `K(1,0)` are disjoint.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1014-L1015
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1014-L1015

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

theorem OrdinalStepUp.ErdosRado.not_inK10_of_inK01 {u : FinChain (n + 3)} (h : InK01 u) : ¬ InK10 u := by sorry
