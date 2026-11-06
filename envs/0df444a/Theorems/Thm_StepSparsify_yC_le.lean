-- Prove2me | Theorems.Thm_StepSparsify_yC_le
-- name    : StepSparsify.yC_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:53:28.493892+00:00
-- url     : https://prove2.me/theorems/774e3a96-9bd8-4137-b41b-794190f66214
-- title:
--   Step Sparsify: y C le
-- statement:
--   y with K = max(k, 3) in the place of k, and with α Calabro's parameter for k and 1/2^s, is at
--   most 1/2^s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalLeaves.lean#L65-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalLeaves.lean#L65-L72

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

theorem StepSparsify.yC_le (k s : ℕ) : Cal.yC (max k 3) (alphaS k s) ≤ 1 / 2 ^ s := by sorry
