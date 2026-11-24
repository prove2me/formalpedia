-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_inP0_of_allUp
-- name    : OrdinalStepUp.ErdosRado.inP0_of_allUp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:49:27.530587+00:00
-- url     : https://prove2.me/theorems/4f94d539-704c-4b07-ac6c-910db20ee22b
-- title:
--   Erdos Rado: in P0 of all Up
-- statement:
--   On a homogeneous all-rising set every chain lies in `P₀`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1164-L1171
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1164-L1171

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

theorem OrdinalStepUp.ErdosRado.inP0_of_allUp (hom : HomAgree 𝒞)
    (hup : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, ∀ c ∈ 𝒞, a ≺w b → b ≺w c → disc a b < disc b c)
    {u : FinChain (n + 4)} (hu : ∀ j, u j ∈ 𝒞) : InP0 u := by sorry
