-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_stepUp_noHomog
-- name    : OrdinalStepUp.ErdosRado.stepUp_noHomog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:49:30.452867+00:00
-- url     : https://prove2.me/theorems/995cdf96-198f-4884-8231-3bba433b2197
-- title:
--   Erdos Rado: step Up no Homog
-- statement:
--   **Theorem 4.18, the negative stepping-up lemma.** If no colour of `g` has a
--   homogeneous set of order type `θ` for `(n+3)`-sets of ordinals, then the
--   stepped-up colouring has none for `(n+4)`-sets of `2^κ`.
--
--   The three cases are [dG21]'s. Colour `1` is the one that absorbs `K(0,1)`
--   and `P(0,1)`, so a homogeneous set for it must avoid `K(1,0)` and then
--   `P(1,0)`; every other colour must avoid `K(0,1)` and `P(0,1)` instead. Either
--   way Lemma 4.16 delivers a `K`-homogeneous `ℬ`, Lemma 4.17 an all-rising `𝒞`
--   inside it, and on `𝒞` the colouring is `g ∘ σ`, so Lemma 4.14 hands
--   back a homogeneous set downstairs -- which was assumed not to exist.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1238-L1302
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1238-L1302

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

theorem OrdinalStepUp.ErdosRado.stepUp_noHomog {g : Finset Ordinal → Set.Iio μ} (hμ : 1 < μ) (hθ : IsIndec θ)
    (hg : NoHomogOrd κ g (n + 3) (θ)) :
    NoHomog κ (stepUpColour (n := n) hμ g) (n + 4) θ := by sorry
