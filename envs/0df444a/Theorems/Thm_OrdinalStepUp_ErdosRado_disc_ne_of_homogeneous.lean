-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_disc_ne_of_homogeneous
-- name    : OrdinalStepUp.ErdosRado.disc_ne_of_homogeneous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:47:30.410992+00:00
-- url     : https://prove2.me/theorems/0c380e7a-5281-45da-af0f-de5ed1a9b613
-- title:
--   Erdos Rado: disc ne of homogeneous
-- statement:
--   In a homogeneous set the auxiliary well-order and the lexicographic order
--   run either together (`K₀`) or exactly opposite (`K₁`). Either way the middle
--   element of a `≺w`-increasing triple lies lexicographically between the outer
--   two, and that is what keeps its two discrepancies apart.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L471-L483
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L471-L483

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

theorem OrdinalStepUp.ErdosRado.disc_ne_of_homogeneous (hA : HomAgree 𝒜)
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜)
    (hab : a ≺w b) (hbc : b ≺w c) : disc a b ≠ disc b c := by sorry
