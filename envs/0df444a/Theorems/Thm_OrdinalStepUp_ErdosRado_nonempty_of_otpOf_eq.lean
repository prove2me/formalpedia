-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_nonempty_of_otpOf_eq
-- name    : OrdinalStepUp.ErdosRado.nonempty_of_otpOf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:47:51.139407+00:00
-- url     : https://prove2.me/theorems/e2d3ef59-8c7f-4577-8aa4-5878b3b21049
-- title:
--   Erdos Rado: nonempty of otp Of eq
-- statement:
--   A set of indecomposable order type is nonempty.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L505-L509
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L505-L509

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

theorem OrdinalStepUp.ErdosRado.nonempty_of_otpOf_eq
    {𝒜 : Set _} (hA : IsIndec (otpOf wo 𝒜)) : 𝒜.Nonempty := by sorry
