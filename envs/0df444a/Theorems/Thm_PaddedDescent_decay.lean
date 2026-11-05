-- Prove2me | Theorems.Thm_PaddedDescent_decay
-- name    : PaddedDescent.decay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:21:28.209369+00:00
-- url     : https://prove2.me/theorems/7a1d027b-15f0-4e07-9e1b-16f50847658e
-- title:
--   Padded Descent: decay
-- statement:
--   t levels, each of which multiplies by 8963/10000, make up for the factor C·(s + 8)⁶·2^s, for
--   every C ≤ 2^10.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L228-L232
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L228-L232

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

theorem PaddedDescent.decay {C : ℕ} (hC : C ≤ 2 ^ 10) (s : ℕ) :
    8963 ^ depthOf s * (C * (s + 8) ^ 6 * 2 ^ s) ≤ 10000 ^ depthOf s := by sorry
