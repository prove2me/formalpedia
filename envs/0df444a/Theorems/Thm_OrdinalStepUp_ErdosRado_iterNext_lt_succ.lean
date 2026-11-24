-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_iterNext_lt_succ
-- name    : OrdinalStepUp.ErdosRado.iterNext_lt_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:49:02.946509+00:00
-- url     : https://prove2.me/theorems/16c35ed5-0550-4e76-93cf-0108352f809a
-- title:
--   Erdos Rado: iter Next lt succ
-- statement:
--   The Erdos Rado construction uses the iter Next lt succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L920-L924
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L920-L924

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

theorem OrdinalStepUp.ErdosRado.iterNext_lt_succ {𝒜 : Set SetOrd} {x : SetOrd} (hA : IsIndec (otp 𝒜))
    (hx : x ∈ 𝒜) (k : ℕ) :
    iterNext 𝒜 x k ≺w iterNext 𝒜 x (k + 1) := by sorry
