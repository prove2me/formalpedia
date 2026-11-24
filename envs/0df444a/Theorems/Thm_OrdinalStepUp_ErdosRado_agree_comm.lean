-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_agree_comm
-- name    : OrdinalStepUp.ErdosRado.agree_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:19.021781+00:00
-- url     : https://prove2.me/theorems/d87c132d-3339-4d01-aad8-bdd35288febd
-- title:
--   Erdos Rado: agree comm
-- statement:
--   The Erdos Rado construction uses the agree comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L192-L199
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L192-L199

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

theorem OrdinalStepUp.ErdosRado.agree_comm : Agree a b ↔ Agree b a := by sorry
