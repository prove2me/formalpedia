-- Prove2me | Theorems.Thm_PaddedDescent_lt_two_pow_mul_div_add_one
-- name    : PaddedDescent.lt_two_pow_mul_div_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:41:20.983936+00:00
-- url     : https://prove2.me/theorems/9f61e9fc-776f-4abe-bd00-151ddde324e6
-- title:
--   Padded Descent: lt two pow mul div add one
-- statement:
--   n < 2^s·(⌊n/2^s⌋ + 1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L175-L176
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L175-L176

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

theorem PaddedDescent.lt_two_pow_mul_div_add_one (n s : ℕ) : n < 2 ^ s * (n / 2 ^ s + 1) := by sorry
