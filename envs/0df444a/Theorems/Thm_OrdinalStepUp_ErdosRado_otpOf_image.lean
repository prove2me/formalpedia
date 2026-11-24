-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_otpOf_image
-- name    : OrdinalStepUp.ErdosRado.otpOf_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:47.560631+00:00
-- url     : https://prove2.me/theorems/b867af6b-7605-4736-8a5c-382a91ff2705
-- title:
--   Erdos Rado: otp Of image
-- statement:
--   A map that is strictly increasing on `𝒜` is an order isomorphism onto its
--   image, so it carries the order type across unchanged.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L623-L630
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L623-L630

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

theorem OrdinalStepUp.ErdosRado.otpOf_image {𝒜 : Set _} {f} (hf : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, wo.r a b → wo'.r (f a) (f b)) :
    otpOf wo' (f '' 𝒜) = otpOf wo 𝒜 := by sorry
