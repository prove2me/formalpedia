-- Prove2me | Theorems.Thm_UniformInK_Budget_leafCU_add_two_le
-- name    : UniformInK.Budget.leafCU_add_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:05:30.517841+00:00
-- url     : https://prove2.me/theorems/7eb38a5e-f1a5-451f-a8f0-ed791932b9b6
-- title:
--   Budget: leaf CU add two le
-- statement:
--   2·(θ 0 + … + θ (k-1)) + 2 ≤ τ^(2k) for k ≥ 1 and τ ≥ 8.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Budget.lean#L30-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Budget.lean#L30-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_PaddedDescent_Choice
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_UniformInK_Top_Budget
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open UniformInK UniformInK.Budget
open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.ParityChecks.BudgetOL UniformInK.Leaves

theorem UniformInK.Budget.leafCU_add_two_le {τ : ℕ} (hτ : 8 ≤ τ) {k : ℕ} (hk : 1 ≤ k) : leafCU τ k + 2 ≤ τ ^ (2 * k) := by sorry
