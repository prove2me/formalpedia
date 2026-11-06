-- Prove2me | Theorems.Thm_StepSparsify_yC_mono
-- name    : StepSparsify.yC_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:52:45.978197+00:00
-- url     : https://prove2.me/theorems/db120dc8-987b-4de4-9321-2b4947086bc0
-- title:
--   Step Sparsify: y C mono
-- statement:
--   y grows with k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalLeaves.lean#L54-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalLeaves.lean#L54-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_StepSparsify_CalNumbers
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Real
import Definitions.Def_SparsificationLemma_Cal_Facts
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_StepSparsify_CalLeaves
set_option autoImplicit false
section
section
open StepSparsify
open Finset Groundwork Groundwork.Sparsify CountKSat SparsificationLemma

theorem StepSparsify.yC_mono {k K : ℕ} (α : ℕ) (hk : 1 ≤ k) (hK : k ≤ K) (hα : 1 ≤ α) : Cal.yC k α ≤ Cal.yC K α := by sorry
