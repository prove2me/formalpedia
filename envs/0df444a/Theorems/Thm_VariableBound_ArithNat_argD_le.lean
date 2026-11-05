-- Prove2me | Theorems.Thm_VariableBound_ArithNat_argD_le
-- name    : VariableBound.ArithNat.argD_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:50:29.95561+00:00
-- url     : https://prove2.me/theorems/e05cfdf3-520d-4061-b27b-4e55111a1a3f
-- title:
--   Arith Nat: arg D le
-- statement:
--   Step 4, «the numbers L and B' are polynomial in n»: K·(λ + B') ≤ 2^(5·17·C₀·Y + 16), for k ≤ β,
--   β + 3 ≤ 2^β ≤ n + 1, 2 ≤ K and K^17 ≤ n < K^(17·C₀).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNat.lean#L106-L160
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNat.lean#L106-L160

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

theorem VariableBound.ArithNat.argD_le (hB : StBounds) (hkβ : k ≤ β) (hbD : β + 3 ≤ 2 ^ β) (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) (hD : 2 ^ β ≤ n + 1) :
    K * (lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) + bitsS K (3 * K ^ 8) (PbD K n (2 ^ β)) (BbD k n))
      ≤ 2 ^ (5 * (17 * C₀ * K.size) + 16) := by sorry
