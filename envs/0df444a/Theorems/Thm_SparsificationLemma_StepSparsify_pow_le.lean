-- Prove2me | Theorems.Thm_SparsificationLemma_StepSparsify_pow_le
-- name    : SparsificationLemma.StepSparsify.pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:54:35.024611+00:00
-- url     : https://prove2.me/theorems/a7e2f49b-dc31-4396-8250-8cb38cd3658b
-- title:
--   Step Sparsify: pow le
-- statement:
--   «(2n+1)^k ≤ n^(2k)», for n ≥ 3.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/StepSparsify.lean#L79-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/StepSparsify.lean#L79-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_StepSparsifyDefs
import Definitions.Def_SparsificationLemma_Nodes
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_SparsificationLemma_Cal_Main
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Real
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_SparsificationLemma_Cal_Facts
import Definitions.Def_SparsificationLemma_Cal_Thr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_StepSparsify
set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.StepSparsify
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate SparsificationLemma.Cal
variable {k n : ℕ} {ε : ℚ} {φ : PFml}

theorem SparsificationLemma.StepSparsify.pow_le (hn : 3 ≤ n) (k : ℕ) : (2 * n + 1) ^ k ≤ n ^ (2 * k) := by sorry
