-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_exists_chain_discSeq
-- name    : OrdinalStepUp.ErdosRado.exists_chain_discSeq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:48:56.531381+00:00
-- url     : https://prove2.me/theorems/1d416e9a-dd4d-4e37-86ff-4d597b84f46a
-- title:
--   Erdos Rado: exists chain disc Seq
-- statement:
--   Lemma 4.14, transfer half. Every chain of discrepancies in the image comes
--   from a chain of points of `𝒟` one longer: pull each value back through
--   `discNext` (which reflects the order, so the points come out in the right
--   order), then append the next point after the top one.
--
--   This is [dG21]'s `{δ_i | i < r - 1} = σ ({h_{ξᵢ} | i < r})`, with the last
--   index `ξ_{r-1} = ξ_{r-2} + 1` appearing here as `nextIn`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L717-L763
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L717-L763

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

theorem OrdinalStepUp.ErdosRado.exists_chain_discSeq (hD : IsIndec (otp 𝒟))
    (hup : ∀ a ∈ 𝒟, ∀ b ∈ 𝒟, ∀ c ∈ 𝒟, a ≺w b → b ≺w c → disc a b < disc b c)
    (w : Fin (n + 1) → Ordinal) (hmono : StrictMono w)
    (hw : ∀ i, w i ∈ discNext 𝒟 '' 𝒟) :
    ∃ u : FinChain (n + 2), (∀ i, u i ∈ 𝒟) ∧ ∀ j, discSeq u j = w j := by sorry
