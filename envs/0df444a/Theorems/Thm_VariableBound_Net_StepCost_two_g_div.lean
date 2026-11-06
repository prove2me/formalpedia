-- Prove2me | Theorems.Thm_VariableBound_Net_StepCost_two_g_div
-- name    : VariableBound.Net.StepCost.two_g_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:54:45.051843+00:00
-- url     : https://prove2.me/theorems/35b566bb-f86e-4a74-b1a8-f676f1181a47
-- title:
--   Step Cost: two g div
-- statement:
--   2g/K = 6K⁷ for g = 3K⁸ and K ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/StepCost.lean#L34-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/StepCost.lean#L34-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_TopNet
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_StepCost
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.StepCost
open Groundwork ClauseBound.Alg

theorem VariableBound.Net.StepCost.two_g_div {K : ℕ} (hK : 1 ≤ K) : 2 * (3 * K ^ 8) / K = 6 * K ^ 7 := by sorry
