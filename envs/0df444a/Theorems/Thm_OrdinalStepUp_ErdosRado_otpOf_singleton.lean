-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_otpOf_singleton
-- name    : OrdinalStepUp.ErdosRado.otpOf_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:37.694368+00:00
-- url     : https://prove2.me/theorems/29421d47-9247-419e-98c6-fc1030015dd5
-- title:
--   Erdos Rado: otp Of singleton
-- statement:
--   A singleton has order type `1`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L486-L486
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L486-L486

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

theorem OrdinalStepUp.ErdosRado.otpOf_singleton {v}: otpOf wo {v} = 1 := by sorry
