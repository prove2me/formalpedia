-- Prove2me | Theorems.Thm_VariableBound_ArithNat_bitsS_eq
-- name    : VariableBound.ArithNat.bitsS_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:05:03.330872+00:00
-- url     : https://prove2.me/theorems/e79cc450-da06-4557-8f2b-468b8a3b7b5a
-- title:
--   Arith Nat: bits S eq
-- statement:
--   The bound B' = `bitsS` for the bit length of the entries of the rebalanced instance, for g = 3K⁸
--   and K ≥ 1: B' = P·6K⁷ + B·(6K⁸ + 36K^15). The paper's B' is ⌈2gP/K⌉ + g²·B = 6K⁷·P + 9K^16·B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNat.lean#L99-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNat.lean#L99-L102

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

theorem VariableBound.ArithNat.bitsS_eq (hK : 1 ≤ K) (P B : ℕ) : bitsS K (3 * K ^ 8) P B = P * (6 * K ^ 7) + B * (6 * K ^ 8 + 36 * K ^ 15) := by sorry
