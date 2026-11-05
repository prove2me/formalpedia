-- Prove2me | Theorems.Thm_UniformInK_Leaves_le_bsumU
-- name    : UniformInK.Leaves.le_bsumU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:20:03.152432+00:00
-- url     : https://prove2.me/theorems/7de2b0c4-73c3-4170-b4e8-fb38d11226cd
-- title:
--   Leaves: le bsum U
-- statement:
--   k ≤ bsumU τ k for τ = 2^(4s+17).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Leaves.lean#L94-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Leaves.lean#L94-L98

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

theorem UniformInK.Leaves.le_bsumU (k s : ℕ) : k ≤ bsumU (tauOf s) k := by sorry
