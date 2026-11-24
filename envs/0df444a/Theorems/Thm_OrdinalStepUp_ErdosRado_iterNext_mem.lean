-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_iterNext_mem
-- name    : OrdinalStepUp.ErdosRado.iterNext_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:10.942095+00:00
-- url     : https://prove2.me/theorems/61f606f6-b649-41bc-8264-591cfee75f46
-- title:
--   Erdos Rado: iter Next mem
-- statement:
--   The Erdos Rado construction uses the iter Next mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L913-L918
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L913-L918

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

theorem OrdinalStepUp.ErdosRado.iterNext_mem {𝒜 : Set SetOrd} {x : SetOrd} (hA : IsIndec (otp 𝒜))
    (hx : x ∈ 𝒜) : ∀ k, iterNext 𝒜 x k ∈ 𝒜
  := by sorry
