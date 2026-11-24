-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_inK_of_homog
-- name    : OrdinalStepUp.ErdosRado.inK_of_homog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:47:31.92298+00:00
-- url     : https://prove2.me/theorems/5f5655d0-c1f6-4497-b9dc-c4f661e3477d
-- title:
--   Erdos Rado: in K of homog
-- statement:
--   On a homogeneous set every chain lies in `K`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1032-L1034
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1032-L1034

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

theorem OrdinalStepUp.ErdosRado.inK_of_homog (h : HomAgree ℬ)
    {u : FinChain (n + 1)} (hu : ∀ i, u i ∈ ℬ) : (InK0 ⊔ InK1) u := by sorry
