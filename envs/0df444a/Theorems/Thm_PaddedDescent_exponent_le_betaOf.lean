-- Prove2me | Theorems.Thm_PaddedDescent_exponent_le_betaOf
-- name    : PaddedDescent.exponent_le_betaOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:03:27.60521+00:00
-- url     : https://prove2.me/theorems/88937220-9b2a-4b6f-b138-364fd0aaadc8
-- title:
--   Padded Descent: exponent le beta Of
-- statement:
--   The inequality between exponents behind the three lemmas that follow: (4s+17)·(2^(k+1) + 1) + k +
--   3 ≤ (s+7)² for s ≥ 2^(k+4).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L93-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L93-L99

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

theorem PaddedDescent.exponent_le_betaOf {k s : ℕ} (hs : s0K k ≤ s) : (4 * s + 17) * (2 ^ (k + 1) + 1) + k + 3 ≤ betaOf s := by sorry
