-- Prove2me | Theorems.Thm_VariableBound_StepChoice_Xsum_nil_le
-- name    : VariableBound.StepChoice.Xsum_nil_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:41:16.150243+00:00
-- url     : https://prove2.me/theorems/23657d7c-9358-4318-ae34-dd5745892ec3
-- title:
--   Step Choice: Xsum nil le
-- statement:
--   For the empty list, X ≤ 2^n·C(m, n̄+1), if there are at most 2^n assignments.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L76-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L76-L86

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

theorem VariableBound.StepChoice.Xsum_nil_le (V : X → Finset E) (nb n : ℕ) (hX : Fintype.card X ≤ 2 ^ n) :
    Xsum V nb [] ≤ 2 ^ n * ((Fintype.card E).choose (nb + 1) : ℤ) := by sorry
