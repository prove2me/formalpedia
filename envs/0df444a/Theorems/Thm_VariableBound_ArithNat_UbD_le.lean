-- Prove2me | Theorems.Thm_VariableBound_ArithNat_UbD_le
-- name    : VariableBound.ArithNat.UbD_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:56:42.497805+00:00
-- url     : https://prove2.me/theorems/3f2a10ac-6156-4f53-9919-7dc679dfc43e
-- title:
--   Arith Nat: Ub D le
-- statement:
--   The bound of Step 3 on the total U, in closed form, for Δ = 2^β: U ≤ 140·k·n·(β+1) + 18·K^16,
--   for β ≥ 1 and n ≥ 1, given `Net.StBounds`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNat.lean#L36-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNat.lean#L36-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_UniformInK_Top_ArithNat
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Budget
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithNat
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open VariableBound VariableBound.ArithNat
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.ArithNat VariableBound.Net
variable {β k K n C₀ : ℕ}

theorem VariableBound.ArithNat.UbD_le (hB : StBounds) (hβ : 1 ≤ β) (hn : 1 ≤ n) : UbD k K n (2 ^ β) ≤ 140 * k * n * (β + 1) + 18 * K ^ 16 := by sorry
