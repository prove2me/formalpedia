-- Prove2me | Theorems.Thm_VariableBound_stNeedD
-- name    : VariableBound.stNeedD
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:51:36.198241+00:00
-- url     : https://prove2.me/theorems/fbaa7a08-06a4-45c6-a336-f64cdffe3433
-- title:
--   Variable Bound: st Need D
-- statement:
--   Steps 4 and 5: the exponent `needD` is at most (140·k·35·k + `ccD k C₀`·A₁ + 1)·n·e·(s+1), if W
--   ≤ A₁·K·e, under the hypotheses listed at `StNeedD`; from the statements on natural numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNeed.lean#L176-L177
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithNeed.lean#L176-L177

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithNeed
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open VariableBound

theorem VariableBound.stNeedD (hU : StUbD) (hA : StArgD) (hL : StLowerD) (hB : UniformInK.StBetaU) : StNeedD := by sorry
