-- Prove2me | Theorems.Thm_UniformInK_Arith_two_pow_s0U_le
-- name    : UniformInK.Arith.two_pow_s0U_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:51:39.840375+00:00
-- url     : https://prove2.me/theorems/f5c2f343-1a33-4333-8411-cbbf64415df0
-- title:
--   Arith: two pow s0 U le
-- statement:
--   2^(s0U k) ≤ 4k².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/ArithTop.lean#L25-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/ArithTop.lean#L25-L31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_UniformInK_Top_ArithTop
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open UniformInK UniformInK.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks

theorem UniformInK.Arith.two_pow_s0U_le {k : ℕ} (hk : 1 ≤ k) : 2 ^ s0U k ≤ 4 * k ^ 2 := by sorry
