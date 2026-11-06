-- Prove2me | Theorems.Thm_SparsificationLemma_StepSparsify_exactly_one
-- name    : SparsificationLemma.StepSparsify.exactly_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:53:58.103561+00:00
-- url     : https://prove2.me/theorems/932ee0ed-a956-4929-9641-6fe4c476e732
-- title:
--   Step Sparsify: exactly one
-- statement:
--   «Each satisfying assignment of the input satisfies exactly one output, and no other assignment
--   satisfies any.»
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/StepSparsify.lean#L87-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/StepSparsify.lean#L87-L88

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

theorem SparsificationLemma.StepSparsify.exactly_one (hk : 3 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) (hφ : IsKCNF k n φ) : ∀ b, ExactlyOne b φ (sparsify k n ε φ) := by sorry
