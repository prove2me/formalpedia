-- Prove2me | Theorems.Thm_VariableBound_StepChoice_second_nonneg
-- name    : VariableBound.StepChoice.second_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:42:21.78114+00:00
-- url     : https://prove2.me/theorems/1d22aae2-8a56-4cfb-bb36-bef245c3bb12
-- title:
--   Step Choice: second nonneg
-- statement:
--   The second term of Υ is not negative.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L198-L200
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L198-L200

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

theorem VariableBound.StepChoice.second_nonneg (nb rb tb : ℕ) (L : List (Finset E)) : 0 ≤ (1 + pp nb) ^ (rb - L.length) * (1 / 2 ^ tb) * ∑ e : E, (2 : ℚ) ^ load L e := by sorry
