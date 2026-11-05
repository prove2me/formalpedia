-- Prove2me | Theorems.Thm_VariableBound_StepChoice_lt_rb
-- name    : VariableBound.StepChoice.lt_rb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:09:18.170046+00:00
-- url     : https://prove2.me/theorems/ab619ae8-15e2-4de2-9a3a-2349d376ce2f
-- title:
--   Step Choice: lt rb
-- statement:
--   A list with X(𝓛) > 0, at most r̄ checks and X(𝓛) ≤ (3/4)^r·2^β has fewer than r̄ checks, because
--   3^r̄·2^β < 4^r̄.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L243-L251
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L243-L251

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

theorem VariableBound.StepChoice.lt_rb (V : X → Finset E) (nb β rb : ℕ) (L : List (Finset E)) (hrb : 3 ^ rb * 2 ^ β < 4 ^ rb) (hl : L.length ≤ rb) (hpos : 0 < Xsum V nb L)
    (h : 4 ^ L.length * Xsum V nb L ≤ 3 ^ L.length * 2 ^ β) : L.length < rb := by sorry
