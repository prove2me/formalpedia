-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_down_forces_down_of_no_inP10
-- name    : OrdinalStepUp.ErdosRado.down_forces_down_of_no_inP10
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:49:28.521132+00:00
-- url     : https://prove2.me/theorems/075befec-a1f5-405b-a5d1-6dfbda9c231a
-- title:
--   Erdos Rado: down forces down of no in P10
-- statement:
--   Lemma 4.17's hypothesis (ii), from `[𝒜]ⁿ⁺⁴ ∩ P(1,0) = ∅`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1124-L1135
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1124-L1135

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

theorem OrdinalStepUp.ErdosRado.down_forces_down_of_no_inP10 (hA : IsIndec (otp 𝒜))
    (hom : HomAgree 𝒜)
    (h : ∀ u : FinChain (n + 4), (∀ i, u i ∈ 𝒜) → ¬ InP10 u) :
    ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, ∀ e ∈ 𝒜, a ≺w b → b ≺w c → c ≺w e →
      disc b c < disc a b → disc c e < disc b c := by sorry
