-- Prove2me | Theorems.Thm_UniformInK_stParU
-- name    : UniformInK.stParU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:20:16.843782+00:00
-- url     : https://prove2.me/theorems/8c5d50f6-e7c5-4ee7-94ad-f918b5798332
-- title:
--   Uniform In K: st Par U
-- statement:
--   leafCU τ k + 2 ≤ 2^(betaU k s) for τ = 2^(4s+17) and k ≥ 1; and k² ≤ τ, 8k ≤ τ if s ≥ s0U k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Budget.lean#L94-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Budget.lean#L94-L105

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
open UniformInK
open PaddedDescent ClauseBound.ParityChecks.BudgetOL UniformInK.Leaves UniformInK.Budget

theorem UniformInK.stParU : StParU := by sorry
