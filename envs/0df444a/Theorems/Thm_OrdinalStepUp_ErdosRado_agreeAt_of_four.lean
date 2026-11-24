-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_agreeAt_of_four
-- name    : OrdinalStepUp.ErdosRado.agreeAt_of_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:09.014824+00:00
-- url     : https://prove2.me/theorems/7b53957c-8b47-4c05-9ac3-8caab3476e54
-- title:
--   Erdos Rado: agree At of four
-- statement:
--   The Erdos Rado construction uses the agree At of four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1067-L1074
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1067-L1074

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

theorem OrdinalStepUp.ErdosRado.agreeAt_of_four {u : FinChain (n + 4)}
    (h0 : u 0 = a) (h1 : u 1 = b) (h2 : u 2 = c) :
    (AgreeAt u 0 ↔ a ≺ b) ∧ (AgreeAt u 1 ↔ b ≺ c) := by sorry
