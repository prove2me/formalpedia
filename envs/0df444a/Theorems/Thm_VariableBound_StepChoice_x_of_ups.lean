-- Prove2me | Theorems.Thm_VariableBound_StepChoice_x_of_ups
-- name    : VariableBound.StepChoice.x_of_ups
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:09:23.004117+00:00
-- url     : https://prove2.me/theorems/ce8b3d13-e38f-4b73-8720-34a2f06dcc22
-- title:
--   Step Choice: x of ups
-- statement:
--   Step 2, «hence X(𝓛) ≤ (3/4)^r·2^β»: from Υ(𝓛) ≤ 2 and β ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L226-L238
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L226-L238

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

theorem VariableBound.StepChoice.x_of_ups (V : X → Finset E) (nb β rb tb : ℕ) (L : List (Finset E)) (hβ : 1 ≤ β) (h : Ups V nb β rb tb L ≤ 2) :
    4 ^ L.length * Xsum V nb L ≤ 3 ^ L.length * 2 ^ β := by sorry
