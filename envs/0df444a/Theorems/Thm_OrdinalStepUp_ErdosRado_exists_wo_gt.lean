-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_exists_wo_gt
-- name    : OrdinalStepUp.ErdosRado.exists_wo_gt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:47:25.844832+00:00
-- url     : https://prove2.me/theorems/e4a133c7-261f-4009-8b25-5225449a2114
-- title:
--   Erdos Rado: exists wo gt
-- statement:
--   A set of indecomposable order type has no greatest element.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L512-L520
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L512-L520

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

theorem OrdinalStepUp.ErdosRado.exists_wo_gt
    {𝒜 : Set _} (hA : IsIndec (otpOf wo 𝒜))
    {v : _} (hv : v ∈ 𝒜) : ∃ w ∈ 𝒜, wo.r v w := by sorry
