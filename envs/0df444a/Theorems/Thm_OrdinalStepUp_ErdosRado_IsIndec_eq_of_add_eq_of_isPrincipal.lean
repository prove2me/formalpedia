-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_IsIndec_eq_of_add_eq_of_isPrincipal
-- name    : OrdinalStepUp.ErdosRado.IsIndec.eq_of_add_eq_of_isPrincipal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:24.64733+00:00
-- url     : https://prove2.me/theorems/1495538d-a729-447e-9f79-d5390d66657d
-- title:
--   Is Indec: eq of add eq of is Principal
-- statement:
--   If `o` is additively principal and splits as `α + β` with `α < o`, then the
--   second summand is all of `o`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L303-L305
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L303-L305

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

theorem OrdinalStepUp.ErdosRado.IsIndec.eq_of_add_eq_of_isPrincipal (hθ : IsIndec θ)
  (hα : α < θ) (h : α + β = θ) : β = θ := by sorry
