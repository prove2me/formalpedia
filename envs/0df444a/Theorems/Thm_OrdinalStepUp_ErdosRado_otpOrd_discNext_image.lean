-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_otpOrd_discNext_image
-- name    : OrdinalStepUp.ErdosRado.otpOrd_discNext_image
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:48:53.047619+00:00
-- url     : https://prove2.me/theorems/40ae8e10-90e6-466f-8cb8-633c0e55b0be
-- title:
--   Erdos Rado: otp Ord disc Next image
-- statement:
--   Lemma 4.14, order-type half. On a `P₀`-homogeneous set of type `θ` the map
--   "discrepancy to the next point" is strictly increasing, so its image -- the
--   source's `𝒜 ⊆ κ` -- has the same order type.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L704-L708
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L704-L708

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

theorem OrdinalStepUp.ErdosRado.otpOrd_discNext_image (hA : IsIndec (otp 𝒜))
    (hup : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c) :
    otpOrd (discNext 𝒜 '' 𝒜) = otp 𝒜 := by sorry
