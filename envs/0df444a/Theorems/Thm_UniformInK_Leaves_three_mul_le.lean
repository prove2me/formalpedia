-- Prove2me | Theorems.Thm_UniformInK_Leaves_three_mul_le
-- name    : UniformInK.Leaves.three_mul_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:50:46.094168+00:00
-- url     : https://prove2.me/theorems/fbe9daa0-d40e-46b7-bd1a-cfabfa587ca6
-- title:
--   Leaves: three mul le
-- statement:
--   3·τ·bsumU τ k ≤ 2^(betaU k s + 4s + 19).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Leaves.lean#L46-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Leaves.lean#L46-L50

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

theorem UniformInK.Leaves.three_mul_le (k s : ℕ) : 3 * tauOf s * bsumU (tauOf s) k ≤ 2 ^ (betaU k s + 4 * s + 19) := by sorry
