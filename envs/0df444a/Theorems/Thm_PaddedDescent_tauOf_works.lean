-- Prove2me | Theorems.Thm_PaddedDescent_tauOf_works
-- name    : PaddedDescent.tauOf_works
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:21:00.542419+00:00
-- url     : https://prove2.me/theorems/55e1ac8c-40b2-4a81-8e65-304640952354
-- title:
--   Padded Descent: tau Of works
-- statement:
--   (k/τ)·log₂(e·τ·bsum τ k) ≤ 1/2^s for τ = 2^(4s+17) and s ≥ s0K k: this is the hypothesis of
--   `WidthK.StLeafCount` with ε = 1/2^s.
--   Indeed e·τ·bsum τ k ≤ 3·τ·bsum τ k ≤ 2^β, and k·β ≤ 2^s·49·4^s ≤ 2^(3s+17).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L145-L170
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Choice.lean#L145-L170

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

theorem PaddedDescent.tauOf_works {k s : ℕ} (hs : s0K k ≤ s) :
    ((k : ℝ) / (tauOf s : ℝ)) * Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsum (tauOf s) k : ℝ)) ≤ 1 / 2 ^ s := by sorry
