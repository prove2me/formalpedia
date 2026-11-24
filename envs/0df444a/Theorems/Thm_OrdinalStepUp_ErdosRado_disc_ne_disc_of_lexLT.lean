-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_disc_ne_disc_of_lexLT
-- name    : OrdinalStepUp.ErdosRado.disc_ne_disc_of_lexLT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:22.179808+00:00
-- url     : https://prove2.me/theorems/52682557-a572-402d-a5c0-50e4d67b1274
-- title:
--   Erdos Rado: disc ne disc of lex LT
-- statement:
--   Consecutive discrepancies along a lexicographically increasing triple are
--   distinct.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L151-L152
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L151-L152

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

theorem OrdinalStepUp.ErdosRado.disc_ne_disc_of_lexLT (hab : a ≺ b) (hbc : b ≺ c) : disc a b ≠ disc b c := by sorry
