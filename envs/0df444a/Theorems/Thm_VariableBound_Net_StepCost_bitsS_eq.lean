-- Prove2me | Theorems.Thm_VariableBound_Net_StepCost_bitsS_eq
-- name    : VariableBound.Net.StepCost.bitsS_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:53:39.473005+00:00
-- url     : https://prove2.me/theorems/e3e59a54-05a2-437e-bca8-b24e4ac6e655
-- title:
--   Step Cost: bits S eq
-- statement:
--   On g = 3K⁸ nodes, K ≥ 1, the number of bits of the program is 6K⁷P + (6K⁸ + 36K¹⁵)B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/StepCost.lean#L38-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/StepCost.lean#L38-L40

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

theorem VariableBound.Net.StepCost.bitsS_eq {K : ℕ} (hK : 1 ≤ K) (P B : ℕ) : bitsS K (3 * K ^ 8) P B = 6 * K ^ 7 * P + (6 * K ^ 8 + 36 * K ^ 15) * B := by sorry
