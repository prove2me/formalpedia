-- Prove2me | Theorems.Thm_VariableBound_StepChoice_load_append
-- name    : VariableBound.StepChoice.load_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:09:18.051015+00:00
-- url     : https://prove2.me/theorems/700a7122-a88c-42b2-bf1f-e6b7f4d5fdec
-- title:
--   Step Choice: load append
-- statement:
--   load(E) for the list (𝓛, Γ) is load(E) for 𝓛 plus [E ∈ Γ].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L148-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/StepChoice.lean#L148-L151

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

theorem VariableBound.StepChoice.load_append (L : List (Finset E)) (Γ : Finset E) (e : E) : load (L ++ [Γ]) e = load L e + if e ∈ Γ then 1 else 0 := by sorry
