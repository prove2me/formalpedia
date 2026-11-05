-- Prove2me | Theorems.Thm_VariableBound_ArithNat_gPD_le_W
-- name    : VariableBound.ArithNat.gPD_le_W
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:51:20.038723+00:00
-- url     : https://prove2.me/theorems/cda24ba0-e0cc-4ef2-988c-2055a99807c3
-- title:
--   Arith Nat: g PD le W
-- statement:
--   g·P ≤ G·W·n, where G = `GD C₀`, for β ≥ 1, 2 ≤ K and K^17 ≤ n < K^(17·C₀).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNat.lean#L73-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNat.lean#L73-L95

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

theorem VariableBound.ArithNat.gPD_le_W (hB : StBounds) (hβ : 1 ≤ β) (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) :
    3 * K ^ 8 * PbD K n (2 ^ β) ≤ GD C₀ * (WofU β K * n) := by sorry
