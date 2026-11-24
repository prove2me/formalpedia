-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_exists_chain_of_four
-- name    : OrdinalStepUp.ErdosRado.exists_chain_of_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:47:30.538729+00:00
-- url     : https://prove2.me/theorems/949a388c-6156-482c-93db-a666f7fe1200
-- title:
--   Erdos Rado: exists chain of four
-- statement:
--   A four-chain of `𝒜` is the front of a chain of length `n + 4`, at the
--   literal indices `0, 1, 2, 3` that `InK01` and `InP01` read.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1038-L1059
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1038-L1059

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

theorem OrdinalStepUp.ErdosRado.exists_chain_of_four (hA : IsIndec (otp 𝒜))
    {a b c e : SetOrd} (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜) (he : e ∈ 𝒜)
    (hab : a ≺w b) (hbc : b ≺w c) (hce : c ≺w e) :
    ∃ u : FinChain (n + 4), (∀ i, u i ∈ 𝒜) ∧
      u 0 = a ∧ u 1 = b ∧ u 2 = c ∧ u 3 = e := by sorry
