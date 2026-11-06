-- Prove2me | Theorems.Thm_VariableBound_Budget_nProf_le
-- name    : VariableBound.Budget.nProf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:51:09.420104+00:00
-- url     : https://prove2.me/theorems/cc6493ab-8f9f-446b-a8c8-f5019292f0b5
-- title:
--   Budget: n Prof le
-- statement:
--   The list of profiles: (M + 1)^(g·g·2) ≤ 2^(g·g·2·size M).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/Budget.lean#L27-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/Budget.lean#L27-L30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_VariableBound_Top_Budget
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_nProf_le
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open VariableBound VariableBound.Budget
open PaddedDescent.F ClauseBound.ParityChecks.BudgetOL

theorem VariableBound.Budget.nProf_le (g M : ℕ) : Mark.nProf g M 2 ≤ 2 ^ (g * g * 2 * Nat.size M) := by sorry
