-- Prove2me | Theorems.Thm_PaddedDescent_three_mul_tauOf_mul_bsum_le
-- name    : PaddedDescent.three_mul_tauOf_mul_bsum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:02:58.446641+00:00
-- url     : https://prove2.me/theorems/394ee1ce-e522-41ae-97a9-48ff958e47e8
-- title:
--   Padded Descent: three mul tau Of mul bsum le
-- statement:
--   3·τ·bsum τ k ≤ 2^β for s ≥ s0K k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L102-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L102-L109

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

theorem PaddedDescent.three_mul_tauOf_mul_bsum_le {k s : ℕ} (hs : s0K k ≤ s) : 3 * tauOf s * bsum (tauOf s) k ≤ 2 ^ betaOf s := by sorry
