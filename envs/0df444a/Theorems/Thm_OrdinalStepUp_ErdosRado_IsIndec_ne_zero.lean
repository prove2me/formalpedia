-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_IsIndec_ne_zero
-- name    : OrdinalStepUp.ErdosRado.IsIndec.ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:26.192287+00:00
-- url     : https://prove2.me/theorems/5b1693c0-819e-4abb-bc53-874031f47d37
-- title:
--   Is Indec: ne zero
-- statement:
--   The Is Indec construction uses the ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L298-L299
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L298-L299

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

theorem OrdinalStepUp.ErdosRado.IsIndec.ne_zero (hθ : IsIndec θ) : θ ≠ 0 := by sorry
