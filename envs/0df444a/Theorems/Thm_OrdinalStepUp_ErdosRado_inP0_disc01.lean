-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_inP0_disc01
-- name    : OrdinalStepUp.ErdosRado.inP0_disc01
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:13.102038+00:00
-- url     : https://prove2.me/theorems/6645a077-ff48-400d-9cf7-d5f309bb6c29
-- title:
--   Erdos Rado: in P0 disc01
-- statement:
--   The Erdos Rado construction uses the in P0 disc01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L991-L992
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L991-L992

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

theorem OrdinalStepUp.ErdosRado.inP0_disc01 {u : FinChain (n + 4)} (h : InP0 u) : discSeq u 0 < discSeq u 1 := by sorry
