-- Prove2me | Theorems.Thm_VariableBound_Arith_const_le
-- name    : VariableBound.Arith.const_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:51:56.534296+00:00
-- url     : https://prove2.me/theorems/35b7ff2a-e237-4ee5-bed5-876ad9ee1ed6
-- title:
--   Arith: const le
-- statement:
--   For k ≥ 1, the constant of `StNeedD` is at most a constant times k².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithTop.lean#L37-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithTop.lean#L37-L47

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

theorem VariableBound.Arith.const_le {k : ℕ} (hk : 1 ≤ k) (C₀ A₁ : ℕ) : 140 * k * (35 * k) + ccD k C₀ * A₁ + 1 ≤ (140 * 35 + (ccD 0 C₀ + 140) * A₁ + 1) * k ^ 2 := by sorry
