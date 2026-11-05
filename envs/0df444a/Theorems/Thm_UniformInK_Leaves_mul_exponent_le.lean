-- Prove2me | Theorems.Thm_UniformInK_Leaves_mul_exponent_le
-- name    : UniformInK.Leaves.mul_exponent_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:50:52.956135+00:00
-- url     : https://prove2.me/theorems/4b40d3be-f7c2-483f-924e-8b5a70df46d6
-- title:
--   Leaves: mul exponent le
-- statement:
--   k·(betaU k s + 4s + 19)·2^s ≤ τ, if 1 ≤ k and k² ≤ 2^s: the left side is at most 4k²·(4s+17)·2^s
--   ≤ 68·2^(3s).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Leaves.lean#L54-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Leaves.lean#L54-L64

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

theorem UniformInK.Leaves.mul_exponent_le {k s : ℕ} (hk : 1 ≤ k) (hs : k ^ 2 ≤ 2 ^ s) : k * (betaU k s + 4 * s + 19) * 2 ^ s ≤ tauOf s := by sorry
