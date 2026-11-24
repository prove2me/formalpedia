-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_discNext_strictMono
-- name    : OrdinalStepUp.ErdosRado.discNext_strictMono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:47:56.957797+00:00
-- url     : https://prove2.me/theorems/63bbf3a9-fbe7-4794-bc0b-995d3d4d0df7
-- title:
--   Erdos Rado: disc Next strict Mono
-- statement:
--   `discNext` is strictly increasing on a `P₀`-homogeneous set of full type.
--   Rewriting the lower value with `discNext_eq` turns this into one instance of
--   the `P₀` hypothesis, on `a ≺ b ≺ nextIn b`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L682-L688
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L682-L688

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

theorem OrdinalStepUp.ErdosRado.discNext_strictMono (hA : IsIndec (otp 𝒜))
    (hup : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c)
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hab : a ≺w b) :
    discNext 𝒜 a < discNext 𝒜 b := by sorry
