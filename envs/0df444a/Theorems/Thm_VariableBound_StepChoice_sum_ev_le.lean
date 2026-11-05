-- Prove2me | Theorems.Thm_VariableBound_StepChoice_sum_ev_le
-- name    : VariableBound.StepChoice.sum_ev_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:41:27.859454+00:00
-- url     : https://prove2.me/theorems/d3850895-0c21-42e7-ab1d-63715a76bdab
-- title:
--   Step Choice: sum ev le
-- statement:
--   For a family as in Lemma 13 with v = n̄, by its part (c): for a set W of more than n̄ clauses, [ |Γ_u
--   ∩ W| even ] is 1 for at most three quarters of the u ∈ Ω.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L92-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L92-L102

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.List
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_StepChoice
set_option autoImplicit false
section
section
open VariableBound VariableBound.StepChoice
open AppVariables Finset
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]

theorem VariableBound.StepChoice.sum_ev_le {nb : ℕ} {Ω : Finset ι} {Γ : ι → Finset E} (hF : IsFamily nb Ω Γ) (W : Finset E) (hW : nb < #W) :
    4 * ∑ u ∈ Ω, ParityChecks.ev #(Γ u ∩ W) ≤ 3 * (#Ω : ℤ) := by sorry
