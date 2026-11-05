-- Prove2me | Theorems.Thm_PaddedDescent_two_pow_betaOf_le_Ktop
-- name    : PaddedDescent.two_pow_betaOf_le_Ktop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:40:58.471497+00:00
-- url     : https://prove2.me/theorems/71955bdc-bd7f-4cb3-bab2-915b3a12e9b5
-- title:
--   Padded Descent: two pow beta Of le Ktop
-- statement:
--   2^(4β + 10s + 1000) ≤ K_t.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L237-L245
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L237-L245

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_SparsifyWidthK_Thresholds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_PaddedDescent_Choice
set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent
open WidthK (theta bsum leafC)
open WidthK.Thresholds

theorem PaddedDescent.two_pow_betaOf_le_Ktop (s : ℕ) : 2 ^ (4 * betaOf s + 10 * s + 1000) ≤ Ktop s := by sorry
