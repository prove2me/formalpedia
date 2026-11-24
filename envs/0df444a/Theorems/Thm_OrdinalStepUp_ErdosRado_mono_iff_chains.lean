-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_mono_iff_chains
-- name    : OrdinalStepUp.ErdosRado.mono_iff_chains
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:48:58.43725+00:00
-- url     : https://prove2.me/theorems/b1f2658a-02ed-491d-bb76-409794236054
-- title:
--   Erdos Rado: mono iff chains
-- statement:
--   The bridge's payoff: a colouring is monochromatic on `𝒜` exactly when it is
--   constant on the chains of `𝒜`. This is what lets the chain-shaped lemmas above
--   meet `ArrowsToOrd`, whose colourings eat `Finset`s.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L839-L849
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L839-L849

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

theorem OrdinalStepUp.ErdosRado.mono_iff_chains {f : Finset SetOrd → Set.Iio μ} {r : ℕ}
    {ι : Set.Iio μ} :
    Mono f r 𝒜 ι ↔ ∀ u : FinChain r, (∀ j, u j ∈ 𝒜) → f u.toFinset = ι := by sorry
