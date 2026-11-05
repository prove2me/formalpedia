-- Prove2me | Theorems.Thm_VariableBound_StepChoice_ups_nil
-- name    : VariableBound.StepChoice.ups_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:42:33.339923+00:00
-- url     : https://prove2.me/theorems/32fb4f99-7e8b-41d0-8d49-14cb91316b5f
-- title:
--   Step Choice: ups nil
-- statement:
--   Step 2, «for the empty list both terms are at most 1, by X ≤ 2^(β−1) and the choice of t̄»: Υ ≤
--   2 for the empty list, if there are at most 2^n assignments, β is the β of the text and
--   m·(1+p)^r̄ ≤ 2^t̄.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L205-L223
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L205-L223

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

theorem VariableBound.StepChoice.ups_nil (V : X → Finset E) (n nb rb tb : ℕ) (hX : Fintype.card X ≤ 2 ^ n) (ht : (Fintype.card E : ℚ) * (1 + pp nb) ^ rb ≤ 2 ^ tb) :
    Ups V nb (beta n (Fintype.card E) nb) rb tb [] ≤ 2 := by sorry
