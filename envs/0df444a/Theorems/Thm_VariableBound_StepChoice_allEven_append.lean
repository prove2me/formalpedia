-- Prove2me | Theorems.Thm_VariableBound_StepChoice_allEven_append
-- name    : VariableBound.StepChoice.allEven_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:41:05.415585+00:00
-- url     : https://prove2.me/theorems/89736db5-1366-4943-911e-6879d1c0ddee
-- title:
--   Step Choice: all Even append
-- statement:
--   Appending the check Γ multiplies the product of ξ by [ |Γ ∩ V(ξ)| even ].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L66-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L66-L68

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
omit [Fintype X] [Fintype E]

theorem VariableBound.StepChoice.allEven_append (V : X → Finset E) (L : List (Finset E)) (Γ : Finset E) (ξ : X) :
    allEven V (L ++ [Γ]) ξ = allEven V L ξ * ParityChecks.ev #(Γ ∩ V ξ) := by sorry
