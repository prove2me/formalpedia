-- Prove2me | Theorems.Thm_UniformInK_ArithNat_WofU_ge
-- name    : UniformInK.ArithNat.WofU_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:50:32.107681+00:00
-- url     : https://prove2.me/theorems/f6c12e1b-7947-41c8-ae93-068aedc9f3f5
-- title:
--   Arith Nat: Wof U ge
-- statement:
--   Lower bounds on `WofU β K`: with b = β + 3, D = 2^β and Y = `K.size`, it is at least b·D, b²·Y,
--   b², b·Y, Y, b, D and 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/ArithNat.lean#L40-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/ArithNat.lean#L40-L59

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

theorem UniformInK.ArithNat.WofU_ge (hK : 1 ≤ K) : (β + 3) * 2 ^ β ≤ WofU β K ∧ (β + 3) ^ 2 * K.size ≤ WofU β K ∧
    (β + 3) ^ 2 ≤ WofU β K ∧ (β + 3) * K.size ≤ WofU β K ∧ K.size ≤ WofU β K ∧ β + 3 ≤ WofU β K ∧ 2 ^ β ≤ WofU β K ∧ 1 ≤ WofU β K := by sorry
