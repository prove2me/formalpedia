-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_not_inK_of_inK01
-- name    : OrdinalStepUp.ErdosRado.not_inK_of_inK01
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:31.936277+00:00
-- url     : https://prove2.me/theorems/98aa20ad-1124-42ba-b030-e4fa39506a1b
-- title:
--   Erdos Rado: not in K of in K01
-- statement:
--   A chain whose pattern begins `0, 1` is in neither `K₀` nor `K₁`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L272-L273
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L272-L273

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

theorem OrdinalStepUp.ErdosRado.not_inK_of_inK01 {u : FinChain (n + 3)} (h : InK01 u) : ¬ (InK0 ⊔ InK1) u := by sorry
