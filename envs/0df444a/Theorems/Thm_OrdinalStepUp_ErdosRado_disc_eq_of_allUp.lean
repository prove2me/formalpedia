-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_disc_eq_of_allUp
-- name    : OrdinalStepUp.ErdosRado.disc_eq_of_allUp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:43.515028+00:00
-- url     : https://prove2.me/theorems/3d7aade7-f035-477a-a7af-b8c2110fc243
-- title:
--   Erdos Rado: disc eq of all Up
-- statement:
--   On an all-`up` set, skipping ahead does not move a discrepancy: the pair
--   `a, c` parts company exactly where `a` and its nearer companion `b` do. This is
--   Observation 4.2 with the `P₀` hypothesis supplying its comparison.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L603-L607
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L603-L607

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

theorem OrdinalStepUp.ErdosRado.disc_eq_of_allUp
    (hB : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c)
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜)
    (hab : a ≺w b) (hbc : b ≺w c) : disc a c = disc a b := by sorry
