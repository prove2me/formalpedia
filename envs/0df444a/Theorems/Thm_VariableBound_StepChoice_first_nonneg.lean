-- Prove2me | Theorems.Thm_VariableBound_StepChoice_first_nonneg
-- name    : VariableBound.StepChoice.first_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:42:15.760623+00:00
-- url     : https://prove2.me/theorems/83664f04-a304-4c54-8c45-03b9b90575d0
-- title:
--   Step Choice: first nonneg
-- statement:
--   The first term of Υ is not negative.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L193-L195
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L193-L195

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
omit [Fintype E]

theorem VariableBound.StepChoice.first_nonneg (V : X → Finset E) (nb β : ℕ) (L : List (Finset E)) : (0 : ℚ) ≤ (4 / 3) ^ L.length * (Xsum V nb L : ℚ) / 2 ^ (β - 1) := by sorry
