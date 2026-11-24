-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_exists_homogeneous
-- name    : OrdinalStepUp.ErdosRado.exists_homogeneous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:48:36.465391+00:00
-- url     : https://prove2.me/theorems/f1b7aea0-2371-4657-9a74-c21145b9fabf
-- title:
--   Erdos Rado: exists homogeneous
-- statement:
--   Lemma 4.16, at the level of pairs: if `𝒜` has order type `θ` and misses
--   one of the two three-point patterns, it has a homogeneous subset of the same
--   order type. The two hypotheses are [dG21]'s (i) and (ii), with `K(0,1)` and
--   `K(1,0)` unwound to the three-chains that witness them.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L434-L457
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L434-L457

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

theorem OrdinalStepUp.ErdosRado.exists_homogeneous (hA : IsIndec (otp 𝒜))
    (h : (¬ ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, a ≺w b ∧ b ≺w c ∧ a ≺ b ∧ ¬ b ≺ c) ∨
         (¬ ∃ a ∈ 𝒜, ∃ b ∈ 𝒜, ∃ c ∈ 𝒜, a ≺w b ∧ b ≺w c ∧ ¬ a ≺ b ∧ b ≺ c)) :
    ∃ ℬ ⊆ 𝒜, otp ℬ = otp 𝒜 ∧ HomAgree ℬ := by sorry
