-- Prove2me | Theorems.Thm_PaddedDescent_decay_step
-- name    : PaddedDescent.decay_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:21:45.922994+00:00
-- url     : https://prove2.me/theorems/973a5e45-6d56-4ff3-bc92-74c08c5b461a
-- title:
--   Padded Descent: decay step
-- statement:
--   Three more units of s: 19 more levels, each of which multiplies by 8963/10000, make up for the
--   factor 8 that 2^s gains and for the growth of
--   (s + 2^15)⁶. The margin is small: (8963/10000)^19·8 = 0.99936…. This is why 2^15 stands here in
--   place of 8: it makes the growth of the sixth power small enough.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L182-L196
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L182-L196

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

theorem PaddedDescent.decay_step (s : ℕ) :
    8963 ^ 19 * (8 * (s + 3 + 2 ^ 15) ^ 6) ≤ 10000 ^ 19 * (s + 2 ^ 15) ^ 6 := by sorry
