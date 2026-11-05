-- Prove2me | Theorems.Thm_VariableBound_stBudgetD
-- name    : VariableBound.stBudgetD
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:51:19.621562+00:00
-- url     : https://prove2.me/theorems/d53fc65a-4e3b-4c57-b308-c81d5e9e2b46
-- title:
--   Variable Bound: st Budget D
-- statement:
--   For k ≥ 1 and s ≥ s0U k, a number F ≥ 2^(restD k K n s) is at least the first, second and fourth
--   budgets, and F + 1 is at least the third, given the bound for the number of leaves
--   (`UniformInK.StLeavesU`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/Budget.lean#L41-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/Budget.lean#L41-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_VariableBound_Top_Budget
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open VariableBound
open PaddedDescent ClauseBound.ParityChecks.BudgetOL UniformInK VariableBound.Net

theorem VariableBound.stBudgetD (hL : StLeavesU) : StBudgetD := by sorry
