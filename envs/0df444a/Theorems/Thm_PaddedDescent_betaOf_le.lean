-- Prove2me | Theorems.Thm_PaddedDescent_betaOf_le
-- name    : PaddedDescent.betaOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:03:05.293764+00:00
-- url     : https://prove2.me/theorems/2e4e8725-20cd-4c0e-8425-1f9f19f9011b
-- title:
--   Padded Descent: beta Of le
-- statement:
--   β ≤ 49·4^s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L138-L140
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L138-L140

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

theorem PaddedDescent.betaOf_le (s : ℕ) : betaOf s ≤ 49 * 2 ^ (2 * s) := by sorry
