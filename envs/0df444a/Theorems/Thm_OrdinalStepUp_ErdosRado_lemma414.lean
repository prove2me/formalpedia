-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_lemma414
-- name    : OrdinalStepUp.ErdosRado.lemma414
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:48:57.192917+00:00
-- url     : https://prove2.me/theorems/b33f4329-537d-4db8-85ae-935f5fe842b6
-- title:
--   Erdos Rado: lemma414
-- statement:
--   Lemma 4.14. A colouring `g` of `r`-sets of `κ`, pulled back along `σ` to
--   `(r+1)`-sets of `2^κ`, and made constant on a `P₀`-homogeneous `𝒟` of type
--   `θ`, is already constant on an `𝒜 ⊆ κ` of type `θ` -- namely the set of
--   `𝒟`'s next-point discrepancies.
--
--   Both halves are in place above: the image has the right order type because
--   `discNext` is strictly increasing, and every `r`-subset of it is some chain's
--   `σ` because chains of discrepancies lift.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L875-L900
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L875-L900

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

theorem OrdinalStepUp.ErdosRado.lemma414 {𝒟 : Set SetOrd} (hD : IsIndec (otp 𝒟))
    (hup : ∀ a ∈ 𝒟, ∀ b ∈ 𝒟, ∀ c ∈ 𝒟, a ≺w b → b ≺w c → disc a b < disc b c)
    (g : Finset Ordinal → Set.Iio μ) (ι : Set.Iio μ)
    (hg : ∀ u : FinChain (n + 2), (∀ j, u j ∈ 𝒟) → g (sigmaOf u) = ι) :
    ∃ 𝒜 : SetOrd, otpOrd 𝒜 = otp 𝒟 ∧ 𝒜 ⊆ ⋃₀ 𝒟 ∧ Mono g (n + 1) 𝒜 ι := by sorry
