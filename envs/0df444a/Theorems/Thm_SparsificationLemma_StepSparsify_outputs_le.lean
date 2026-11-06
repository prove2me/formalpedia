-- Prove2me | Theorems.Thm_SparsificationLemma_StepSparsify_outputs_le
-- name    : SparsificationLemma.StepSparsify.outputs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:09:47.838534+00:00
-- url     : https://prove2.me/theorems/8ca320a7-69e5-4655-b781-d572dcf14e87
-- title:
--   Step Sparsify: outputs le
-- statement:
--   «Applied to a k-CNF on n variables and ε ∈ (0,1], the changed algorithm produces at most 2^(εn)
--   outputs …»; the time is in proof/sparsification/SparsificationLemma/Mach.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/StepSparsify.lean#L73-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/StepSparsify.lean#L73-L74

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.StepSparsify
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate SparsificationLemma.Cal
variable {k n : ℕ} {ε : ℚ} {φ : PFml}

theorem SparsificationLemma.StepSparsify.outputs_le (hk : 3 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) (hφ : IsKCNF k n φ) : ((sparsify k n ε φ).length : ℝ) ≤ (2 : ℝ) ^ ((ε : ℝ) * (n : ℝ)) := by sorry
