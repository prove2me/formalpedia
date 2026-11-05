-- Prove2me | Theorems.Thm_StepSparsify_le_alphaS
-- name    : StepSparsify.le_alphaS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:07:22.02265+00:00
-- url     : https://prove2.me/theorems/29b4c2c5-8a62-40b4-ba54-9cd4218a4923
-- title:
--   Step Sparsify: le alpha S
-- statement:
--   2 ≤ α and K² ≤ α, for all k and s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalNumbers.lean#L61-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalNumbers.lean#L61-L63

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

theorem StepSparsify.le_alphaS (k s : ℕ) : 2 ≤ alphaS k s ∧ max k 3 ^ 2 ≤ alphaS k s := by sorry
