-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_noHomog_stepUp
-- name    : OrdinalStepUp.ErdosRado.noHomog_stepUp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:50:48.657344+00:00
-- url     : https://prove2.me/theorems/2d6ab292-5ac4-429b-90f2-0312ebc6e88a
-- title:
--   Erdos Rado: no Homog step Up
-- statement:
--   **Theorem 4.18 as a negative partition arrow.** If `κ ↛ (ω^α)ʳ⁺³_μ` is
--   witnessed by some colouring of the `(r+3)`-subsets of `κ`, then
--   `2^κ ↛ (ω^α)ʳ⁺⁴_μ` holds one level up -- with the *same* number of colours,
--   since stepping up reuses `0` and `1` rather than introducing any.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1309-L1315
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1309-L1315

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

theorem OrdinalStepUp.ErdosRado.noHomog_stepUp {μ α : Ordinal} (hα : 0 < α) (hμ : 1 < μ)
    (h : ∃ g : Finset Ordinal → Set.Iio μ, NoHomogOrd κ g (r + 3) (ω^α)) :
    ∃ f : Finset (Set Ordinal) → Set.Iio μ, NoHomog κ f (r + 4) (ω^α) := by sorry
