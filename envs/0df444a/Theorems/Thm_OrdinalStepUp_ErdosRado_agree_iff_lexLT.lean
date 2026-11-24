-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_agree_iff_lexLT
-- name    : OrdinalStepUp.ErdosRado.agree_iff_lexLT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:47:30.020214+00:00
-- url     : https://prove2.me/theorems/ce3ff7e1-de64-4300-a24b-8dc9fb583976
-- title:
--   Erdos Rado: agree iff lex LT
-- statement:
--   On a `≺w`-ordered pair, agreement says exactly that `≺` runs the same way.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L190-L190
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L190-L190

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

theorem OrdinalStepUp.ErdosRado.agree_iff_lexLT (hab : a ≺w b) : Agree a b ↔ a ≺ b := by sorry
