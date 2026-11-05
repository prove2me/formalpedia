-- Prove2me | Theorems.Thm_StepSparsify_eps_le_one
-- name    : StepSparsify.eps_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:56:01.488288+00:00
-- url     : https://prove2.me/theorems/7e243e0f-a892-4ea5-9459-c1c334d718be
-- title:
--   Step Sparsify: eps le one
-- statement:
--   ε = 1/2^s is at most 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalNumbers.lean#L56-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalNumbers.lean#L56-L58

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

theorem StepSparsify.eps_le_one (s : ℕ) : (1 : ℚ) / 2 ^ s ≤ 1 := by sorry
