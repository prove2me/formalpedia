-- Prove2me | Theorems.Thm_UniformInK_Budget_stack_le
-- name    : UniformInK.Budget.stack_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:47:50.395429+00:00
-- url     : https://prove2.me/theorems/c4d71f39-964d-4636-9e2e-8b52301ed297
-- title:
--   Budget: stack le
-- statement:
--   The stack of the walk: stackLenCU k τ n (inLen k n) ≤ 2^(betaU k s + 5k + 10 + (k+3)·size n) for
--   τ = 2^(4s+17).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Budget.lean#L48-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Budget.lean#L48-L85

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
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_stack_le
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open UniformInK UniformInK.Budget
open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.ParityChecks.BudgetOL UniformInK.Leaves

theorem UniformInK.Budget.stack_le {k : ℕ} (hk : 1 ≤ k) (n s : ℕ) : stackLenCU k (tauOf s) n (inLen k n) ≤ 2 ^ (betaU k s + 5 * k + 10 + (k + 3) * Nat.size n) := by sorry
