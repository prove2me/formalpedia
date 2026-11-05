-- Prove2me | Theorems.Thm_VariableBound_ArithNat_g_le_n
-- name    : VariableBound.ArithNat.g_le_n
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:06:30.091168+00:00
-- url     : https://prove2.me/theorems/34cddcf9-a1f9-4c97-9ca9-d5b3a66e24f6
-- title:
--   Arith Nat: g le n
-- statement:
--   Step 4, «g ≤ n»: 3K⁸ ≤ n, for 2 ≤ K and K^17 ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNat.lean#L66-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNat.lean#L66-L70

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

theorem VariableBound.ArithNat.g_le_n (hK : 2 ≤ K) (hn17 : K ^ 17 ≤ n) : 3 * K ^ 8 ≤ n := by sorry
