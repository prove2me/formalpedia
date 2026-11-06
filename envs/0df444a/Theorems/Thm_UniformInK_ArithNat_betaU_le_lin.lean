-- Prove2me | Theorems.Thm_UniformInK_ArithNat_betaU_le_lin
-- name    : UniformInK.ArithNat.betaU_le_lin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:51:10.428379+00:00
-- url     : https://prove2.me/theorems/5ea18ea4-774d-45fc-9d9d-cbc9f2708b12
-- title:
--   Arith Nat: beta U le lin
-- statement:
--   β + 1 ≤ 35·k·(s+1) for β = `betaU k s` and k ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/ArithNat.lean#L77-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/ArithNat.lean#L77-L79

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_UniformInK_Top_ArithNat
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open UniformInK UniformInK.ArithNat
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks
variable {β k K n C₀ : ℕ}

theorem UniformInK.ArithNat.betaU_le_lin {k : ℕ} (s : ℕ) (hk : 1 ≤ k) : betaU k s + 1 ≤ 35 * k * (s + 1) := by sorry
