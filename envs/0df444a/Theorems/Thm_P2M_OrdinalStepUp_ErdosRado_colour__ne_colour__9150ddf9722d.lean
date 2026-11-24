-- Prove2me | Theorems.Thm_P2M_OrdinalStepUp_ErdosRado_colour__ne_colour__9150ddf9722d
-- name    : P2M_OrdinalStepUp_ErdosRado_colour__ne_colour__9150ddf9722d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:49:30.836223+00:00
-- url     : https://prove2.me/theorems/7df3d26c-08fc-4ea5-81d7-19d8ec4ed67c
-- title:
--   P2 M Ordinal Step Up Erdos Rado colour  ne colour  9150ddf9722d: P2 M Ordinal Step Up Erdos Rado colour  ne colour  9150ddf9722d
-- statement:
--   The two reserved colours are distinct.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1199-L1200
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L1199-L1200

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

theorem P2M_OrdinalStepUp_ErdosRado_colour__ne_colour__9150ddf9722d (hμ : 1 < μ) : colour₀ hμ ≠ colour₁ hμ := by sorry

alias «OrdinalStepUp».«ErdosRado».«colour₀_ne_colour₁» := P2M_OrdinalStepUp_ErdosRado_colour__ne_colour__9150ddf9722d
