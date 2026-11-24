-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_lexLT_of_not_lexLT
-- name    : OrdinalStepUp.ErdosRado.lexLT_of_not_lexLT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:26.031816+00:00
-- url     : https://prove2.me/theorems/d1fdb329-29b9-4669-b9fc-93703e050cc3
-- title:
--   Erdos Rado: lex LT of not lex LT
-- statement:
--   Distinct points are `≺`-comparable, so failing to increase means decreasing.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L202-L205
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L202-L205

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

theorem OrdinalStepUp.ErdosRado.lexLT_of_not_lexLT (hab : a ≺w b) (h : ¬ a ≺ b) : b ≺ a := by sorry
