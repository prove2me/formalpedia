-- Prove2me | Theorems.Thm_OrdinalStepUp_ErdosRado_disc_eq_of_disc_lt_disc
-- name    : OrdinalStepUp.ErdosRado.disc_eq_of_disc_lt_disc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:48:21.932389+00:00
-- url     : https://prove2.me/theorems/0a012c5f-607e-4007-a082-fe9064ad9074
-- title:
--   Erdos Rado: disc eq of disc lt disc
-- statement:
--   Observation 4.2: the earlier split wins. If `a` and `b` part company
--   strictly before `b` and `c` do, then `a` and `c` part company at exactly the
--   same place as `a` and `b`.
--
--   Source: https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L157-L164
-- source:
--   https://github.com/bjrtx/ordinal-step-up/blob/e46994fca709e3983061ef8d52a824b29a613ee4/OrdinalStepUp/Solution.lean#L157-L164

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

theorem OrdinalStepUp.ErdosRado.disc_eq_of_disc_lt_disc (hab : a ≠ b) (h : disc a b < disc b c) : disc a c = disc a b := by sorry
