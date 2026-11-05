-- Prove2me | Theorems.Thm_StepSparsify_alpha_le
-- name    : StepSparsify.alpha_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:52:30.122946+00:00
-- url     : https://prove2.me/theorems/e25cb2b8-9652-4853-80fb-9baff7a372f9
-- title:
--   Step Sparsify: alpha le
-- statement:
--   32α ≤ τ², for k ≥ 1 and k² ≤ 2^s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalNumbers.lean#L66-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalNumbers.lean#L66-L85

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

theorem StepSparsify.alpha_le {k s : ℕ} (hk : 1 ≤ k) (hs : k ^ 2 ≤ 2 ^ s) : 32 * alphaS k s ≤ tauOf s ^ 2 := by sorry
