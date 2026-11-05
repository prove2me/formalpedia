-- Prove2me | Theorems.Thm_PaddedDescent_decay_aux
-- name    : PaddedDescent.decay_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:21:33.604197+00:00
-- url     : https://prove2.me/theorems/b5af82cc-f7ca-4ada-ad27-87b70ecfe882
-- title:
--   Padded Descent: decay aux
-- statement:
--   8963^(⌊19s/3⌋+700)·2^10·(s + 2^15)⁶·2^s ≤ 10000^(⌊19s/3⌋+700): by induction in steps of 3, from
--   s = 0, 1, 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L219-L224
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L219-L224

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

theorem PaddedDescent.decay_aux : ∀ s : ℕ,
    8963 ^ (19 * s / 3 + 700) * (2 ^ 10 * (s + 2 ^ 15) ^ 6 * 2 ^ s) ≤ 10000 ^ (19 * s / 3 + 700)
  := by sorry
