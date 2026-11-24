-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_nonempty_splitIso
-- name    : OrdinalStepUp.ErdosRado.nonempty_splitIso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:27.101514+00:00
-- url     : https://prove2.me/theorems/9002f134-d017-4605-9fb6-14ec8f7b6e0b
-- title:
--   Erdos Rado: nonempty split Iso
-- statement:
--   **As well-orders, `𝒜` is `𝒜 \ ℬ` followed by `ℬ`.** If `ℬ` is a final
--   segment of `𝒜` then everything outside it precedes everything inside, so `𝒜`
--   is the lexicographic sum of the two pieces.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L321-L351
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L321-L351

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

theorem OrdinalStepUp.ErdosRado.nonempty_splitIso {𝒜 ℬ : Set wo.α} (hBA : ℬ ⊆ 𝒜)
    (hfinal : ∀ y ∈ ℬ, ∀ x ∈ 𝒜, wo.r y x → x ∈ ℬ) :
    Nonempty (Sum.Lex (Subrel wo.r (· ∈ 𝒜 \ ℬ)) (Subrel wo.r (· ∈ ℬ))
      ≃r Subrel wo.r (· ∈ 𝒜)) := by sorry
