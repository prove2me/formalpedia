-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_wo_of_discNext_lt
-- name    : OrdinalStepUp.ErdosRado.wo_of_discNext_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:48:49.289899+00:00
-- url     : https://prove2.me/theorems/f1a8041f-e00e-4886-9e23-a4af3c4b9852
-- title:
--   Erdos Rado: wo of disc Next lt
-- statement:
--   The converse: `discNext` reflects the order, so a chain of values pulls back
--   to a chain of points. With `discNext_strictMono` this makes `discNext` an order
--   isomorphism onto its image.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L693-L699
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L693-L699

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

theorem OrdinalStepUp.ErdosRado.wo_of_discNext_lt (hA : IsIndec (otp 𝒜))
    (hup : ∀ a ∈ 𝒜, ∀ b ∈ 𝒜, ∀ c ∈ 𝒜, a ≺w b → b ≺w c → disc a b < disc b c)
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (h : discNext 𝒜 a < discNext 𝒜 b) :
    a ≺w b := by sorry
