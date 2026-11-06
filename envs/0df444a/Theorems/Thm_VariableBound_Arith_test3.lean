-- Prove2me | Theorems.Thm_VariableBound_Arith_test3
-- name    : VariableBound.Arith.test3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:50:35.299533+00:00
-- url     : https://prove2.me/theorems/5853d10f-fb98-4446-8015-6cf83390712f
-- title:
--   Arith: test3
-- statement:
--   The third test of the plan, 29·⌈log₂(2Δ)⌉ + 19 ≤ n for Δ = 2^β, is passed if β + 3 ≤ 2^β and
--   (2^β)⁶ ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithTop.lean#L57-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithTop.lean#L57-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_UniformInK_Top_ArithTop
import Definitions.Def_UniformInK_Top_ArithTop
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithTop
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open VariableBound VariableBound.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.Arith

theorem VariableBound.Arith.test3 {β n : ℕ} (hb : β + 3 ≤ 2 ^ β) (h6 : (2 ^ β) ^ 6 ≤ n) : 29 * LD (2 ^ β) + 19 ≤ n := by sorry
