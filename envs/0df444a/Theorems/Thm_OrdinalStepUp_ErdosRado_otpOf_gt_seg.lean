-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_otpOf_gt_seg
-- name    : OrdinalStepUp.ErdosRado.otpOf_gt_seg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:47:54.820809+00:00
-- url     : https://prove2.me/theorems/0452e8c0-3858-411c-9bfb-1c97a18ea4d9
-- title:
--   Erdos Rado: otp Of gt seg
-- statement:
--   The part of `𝒜` strictly above one of its points still has order type
--   `θ`. This is `otpOf_final_seg_at` with the cut point itself removed: the
--   removed part has type `1`, and `θ` absorbs it.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L491-L502
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L491-L502

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

theorem OrdinalStepUp.ErdosRado.otpOf_gt_seg
    {𝒜 : Set _} (hA : IsIndec (otpOf wo 𝒜))
    {v : wo.α} (hv : v ∈ 𝒜) : otpOf wo {x ∈ 𝒜 | wo.r v x} = otpOf wo 𝒜 := by sorry
