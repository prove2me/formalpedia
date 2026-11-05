-- Prove2me | Theorems.Thm_VariableBound_ArithNat_lowerD
-- name    : VariableBound.ArithNat.lowerD
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:55:12.529532+00:00
-- url     : https://prove2.me/theorems/93928455-f8e3-4486-a0c9-d4c21af3784d
-- title:
--   Arith Nat: lower D
-- statement:
--   Step 4, «all these are o(en)», first half: the parts of lower order of the exponent, each
--   multiplied by K, are at most a number times W·n; the number depends on C₀ only, except 19 + 140·k +
--   G, where G = `GD C₀`, for the part
--   (K − 1)·λ; for 1 ≤ β, k ≤ β, 2 ≤ K and K^17 ≤ n < K^(17·C₀), given `Net.StBounds`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNat.lean#L196-L297
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNat.lean#L196-L297

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

theorem VariableBound.ArithNat.lowerD (hB : StBounds) (hβ : 1 ≤ β) (hkb : k ≤ β) (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) (hlt : n < K ^ (17 * C₀)) :
    K * (3 * K ^ 8 * K.size) ≤ 3 * (WofU β K * n) ∧
    K * (PbD K n (2 ^ β) * (2 * (3 * K ^ 8) / K + 1)) ≤ 3 * GD C₀ * (WofU β K * n) ∧
    K * ((K - 1) * lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β))) ≤ (19 + 140 * k + GD C₀) * (WofU β K * n) ∧
    3 * K ^ 8 * PbD K n (2 ^ β) ≤ GD C₀ * (WofU β K * n) ∧
    K * (18 * K ^ 16) ≤ 18 * (WofU β K * n) ∧
    K * K ^ 2 ≤ WofU β K * n ∧
    K * (C₀ * K ^ 2 * (5 * (17 * C₀ * K.size) + 16)) ≤ C₀ * (85 * C₀ + 16) * (WofU β K * n) ∧
    K * (3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n (2 ^ β))) ≤ 18 * (4 + 17 * C₀) * (WofU β K * n) ∧
    K * (Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ β) + 1) * (Nat.size (2 ^ β * n) + 2) + 8) + 2 + (β + 5 * k + 10 + (k + 3) * n.size)) ≤
      (10 + 34 * C₀) * (WofU β K * n) := by sorry
