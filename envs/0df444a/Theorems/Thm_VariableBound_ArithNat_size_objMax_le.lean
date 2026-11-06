-- Prove2me | Theorems.Thm_VariableBound_ArithNat_size_objMax_le
-- name    : VariableBound.ArithNat.size_objMax_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:51:27.27796+00:00
-- url     : https://prove2.me/theorems/f6fffca0-d8a8-4d28-8824-2d2d36254e57
-- title:
--   Arith Nat: size obj Max le
-- statement:
--   The bit length of the bound for the number of objects, for Δ = 2^β: at most 2β + size n + 10.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNat.lean#L163-L172
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNat.lean#L163-L172

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

theorem VariableBound.ArithNat.size_objMax_le (β n : ℕ) : Nat.size (objMax n (2 ^ β)) ≤ 2 * β + n.size + 10 := by sorry
