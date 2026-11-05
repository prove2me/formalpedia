-- Prove2me | Theorems.Thm_PaddedDescent_decay_aux_step
-- name    : PaddedDescent.decay_aux_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:21:22.294741+00:00
-- url     : https://prove2.me/theorems/da06bd1d-7e0f-4bf8-b82c-c901e4d6fdb9
-- title:
--   Padded Descent: decay aux step
-- statement:
--   From s to s + 3 in `decay_aux`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L199-L215
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L199-L215

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

theorem PaddedDescent.decay_aux_step {s : ℕ} (ih : 8963 ^ (19 * s / 3 + 700) * (2 ^ 10 * (s + 2 ^ 15) ^ 6 * 2 ^ s) ≤ 10000 ^ (19 * s / 3 + 700)) :
    8963 ^ (19 * (s + 3) / 3 + 700) * (2 ^ 10 * (s + 3 + 2 ^ 15) ^ 6 * 2 ^ (s + 3)) ≤ 10000 ^ (19 * (s + 3) / 3 + 700) := by sorry
