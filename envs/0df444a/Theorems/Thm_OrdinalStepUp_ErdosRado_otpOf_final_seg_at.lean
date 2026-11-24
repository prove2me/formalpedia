-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_otpOf_final_seg_at
-- name    : OrdinalStepUp.ErdosRado.otpOf_final_seg_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:47:46.211559+00:00
-- url     : https://prove2.me/theorems/6878a114-53d6-486f-aa29-467a899613ce
-- title:
--   Erdos Rado: otp Of final seg at
-- statement:
--   Lemma 4.15 in the form [dG21] actually uses it: the final segment of
--   `𝒜` cut at a point `x₀ ∈ 𝒜` has the same order type `θ` as `𝒜` itself.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L380-L385
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L380-L385

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

theorem OrdinalStepUp.ErdosRado.otpOf_final_seg_at
    {𝒜 : Set _} (hA : IsIndec (otpOf wo 𝒜)) (hx : x ∈ 𝒜) :
    otpOf wo {y ∈ 𝒜 | ¬ wo.r y x} = otpOf wo 𝒜 := by sorry
