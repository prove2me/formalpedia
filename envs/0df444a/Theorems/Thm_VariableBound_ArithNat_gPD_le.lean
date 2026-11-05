-- Prove2me | Theorems.Thm_VariableBound_ArithNat_gPD_le
-- name    : VariableBound.ArithNat.gPD_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:05:05.867984+00:00
-- url     : https://prove2.me/theorems/5e572c5d-b590-4dea-9c03-802a131c334c
-- title:
--   Arith Nat: g PD le
-- statement:
--   The bound of Step 3 on g·P, in closed form, for Δ = 2^β: g·P ≤ n·2^β·(842·(β+3) + 4·size n), for
--   β ≥ 1, n ≥ 1 and g = 3K⁸ ≤ n, given `Net.StBounds`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNat.lean#L44-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNat.lean#L44-L63

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

theorem VariableBound.ArithNat.gPD_le (hB : StBounds) (hβ : 1 ≤ β) (hn : 1 ≤ n) (hg : 3 * K ^ 8 ≤ n) :
    3 * K ^ 8 * PbD K n (2 ^ β) ≤ n * 2 ^ β * (842 * (β + 3) + 4 * n.size) := by sorry
