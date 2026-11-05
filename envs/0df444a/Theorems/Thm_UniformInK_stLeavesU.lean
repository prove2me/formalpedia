-- Prove2me | Theorems.Thm_UniformInK_stLeavesU
-- name    : UniformInK.stLeavesU
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:04:22.296168+00:00
-- url     : https://prove2.me/theorems/a29deac6-0877-4d57-a745-4ff77754806e
-- title:
--   Uniform In K: st Leaves U
-- statement:
--   Σ_{j ≤ kn/τ} C(bsumU τ k · n, j) ≤ 2^(⌊n/2^s⌋+1) for τ = 2^(4s+17), k ≥ 1 and s ≥ s0U k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Leaves.lean#L107-L121
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Leaves.lean#L107-L121

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
open UniformInK
open PaddedDescent UniformInK.Leaves

theorem UniformInK.stLeavesU : StLeavesU := by sorry
