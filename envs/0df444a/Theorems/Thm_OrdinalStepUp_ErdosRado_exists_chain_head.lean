-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_exists_chain_head
-- name    : OrdinalStepUp.ErdosRado.exists_chain_head
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:49:07.49235+00:00
-- url     : https://prove2.me/theorems/73817990-0908-4f7f-92ca-ff955a847978
-- title:
--   Erdos Rado: exists chain head
-- statement:
--   Any nonempty chain of a set of full order type is the front of a chain of
--   any greater length: keep the head and pad above its top by iterating `nextIn`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L938-L973
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L938-L973

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

theorem OrdinalStepUp.ErdosRado.exists_chain_head {𝒜 : Set SetOrd} {j L : ℕ} (hA : IsIndec (otp 𝒜))
    (hjL : j + 1 ≤ L) (v : Fin (j + 1) → SetOrd) (hv : ∀ i, v i ∈ 𝒜)
    (hvmono : ∀ i i' : Fin (j + 1), i < i' → v i ≺w v i') :
    ∃ u : FinChain L, (∀ i, u i ∈ 𝒜) ∧
      ∀ i : Fin (j + 1), u ⟨i, lt_of_lt_of_le i.isLt hjL⟩ = v i := by sorry
