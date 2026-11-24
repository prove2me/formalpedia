-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_disc_lt_disc_of_allUp
-- name    : OrdinalStepUp.ErdosRado.disc_lt_disc_of_allUp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:50:04.407097+00:00
-- url     : https://prove2.me/theorems/28a487f3-3387-4617-a523-233190121313
-- title:
--   Erdos Rado: disc lt disc of all Up
-- statement:
--   On an all-`up` set, discrepancies of disjoint pairs compare: from `a ≺w b`,
--   `b = c` or `b ≺w c`, and `c ≺w e`, it follows that `disc a b < disc c e`. With
--   `b = c` this is the hypothesis itself; with `b ≺w c` it is two applications
--   chained.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L613-L619
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L613-L619

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

theorem OrdinalStepUp.ErdosRado.disc_lt_disc_of_allUp
    (hB : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c)
    {a b c e : SetOrd} (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜) (he : e ∈ 𝒜)
    (hab : a ≺w b) (hbc : b = c ∨ b ≺w c) (hce : c ≺w e) : disc a b < disc c e := by sorry
