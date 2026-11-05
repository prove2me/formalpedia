-- Prove2me | Theorems.Thm_VariableBound_Ineq_lg_one_add_le
-- name    : VariableBound.Ineq.lg_one_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:19.930953+00:00
-- url     : https://prove2.me/theorems/6b1e5727-7b44-4c43-a2c2-5f28bed40bb4
-- title:
--   Ineq: lg one add le
-- statement:
--   log(1+p) ≤ (3/2)·p for p ≥ 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L178-L185
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Params/Ineq.lean#L178-L185

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Ineq
set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq

theorem VariableBound.Ineq.lg_one_add_le {p : ℝ} (hp : 0 ≤ p) : lg (1 + p) ≤ 3 / 2 * p := by sorry
