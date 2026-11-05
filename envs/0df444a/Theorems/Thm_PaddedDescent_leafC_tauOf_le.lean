-- Prove2me | Theorems.Thm_PaddedDescent_leafC_tauOf_le
-- name    : PaddedDescent.leafC_tauOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:03:16.833629+00:00
-- url     : https://prove2.me/theorems/5ad31348-d82d-4579-bcb6-27c3e033521d
-- title:
--   Padded Descent: leaf C tau Of le
-- statement:
--   leafC τ k ≤ 2k·2^((4s+17)·2^k).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L72-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L72-L77

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

theorem PaddedDescent.leafC_tauOf_le (k s : ℕ) : leafC (tauOf s) k ≤ 2 * (k * 2 ^ ((4 * s + 17) * 2 ^ k)) := by sorry
