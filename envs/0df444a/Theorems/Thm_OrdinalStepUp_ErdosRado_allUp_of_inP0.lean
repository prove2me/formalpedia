-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_allUp_of_inP0
-- name    : OrdinalStepUp.ErdosRado.allUp_of_inP0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:50:38.909369+00:00
-- url     : https://prove2.me/theorems/6e9de86b-ca90-440c-91fc-fbaa86f3b033
-- title:
--   Erdos Rado: all Up of in P0
-- statement:
--   From "every chain lies in `P₀`" to the pointwise form Lemma 4.14 wants.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1138-L1146
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1138-L1146

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

theorem OrdinalStepUp.ErdosRado.allUp_of_inP0 (hA : IsIndec (otp 𝒜))
    (h : ∀ u : FinChain (n + 4), (∀ i, u i ∈ 𝒜) → InP0 u) :
    ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c := by sorry
