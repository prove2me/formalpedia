-- Prove2me | Theorems.Thm_StepSparsify_stCalNumbers
-- name    : StepSparsify.stCalNumbers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:52:48.888183+00:00
-- url     : https://prove2.me/theorems/9afabf1f-e89a-46c8-983b-958fd6397d27
-- title:
--   Step Sparsify: st Cal Numbers
-- statement:
--   Calabro's numbers fit the bounds of the plan: 1 ≤ α, k² ≤ α, and the two sums are small enough.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalNumbers.lean#L88-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalNumbers.lean#L88-L124

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_UniformInK_Top_Leaves
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_StepSparsify_CalNumbers
set_option autoImplicit false
section
section
open StepSparsify
open Finset PaddedDescent UniformInK SparsificationLemma

theorem StepSparsify.stCalNumbers : StCalNumbers := by sorry
