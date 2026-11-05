-- Prove2me | Theorems.Thm_UniformInK_Leaves_tauOf_worksU
-- name    : UniformInK.Leaves.tauOf_worksU
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T00:56:30.990878+00:00
-- url     : https://prove2.me/theorems/9529cfb8-f866-4dac-b053-3aa60f1a0d46
-- title:
--   Leaves: tau Of works U
-- statement:
--   (k/τ)·log₂(e·τ·bsumU τ k) ≤ 1/2^s for τ = 2^(4s+17), 1 ≤ k and s ≥ s0U k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Leaves.lean#L67-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Leaves.lean#L67-L91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_PaddedDescent_Choice
import Definitions.Def_SparsifyWidthK_Thresholds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_UniformInK_Top_Leaves
set_option autoImplicit false
section
open UniformInK UniformInK.Leaves
open PaddedDescent

theorem UniformInK.Leaves.tauOf_worksU {k s : ℕ} (hk : 1 ≤ k) (hs : s0U k ≤ s) :
    ((k : ℝ) / (tauOf s : ℝ)) * Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsumU (tauOf s) k : ℝ)) ≤ 1 / 2 ^ s := by sorry
