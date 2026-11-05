-- Prove2me | Theorems.Thm_UniformInK_Leaves_bsumU_tauOf
-- name    : UniformInK.Leaves.bsumU_tauOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:46:15.517112+00:00
-- url     : https://prove2.me/theorems/e937f45f-accc-4bb3-b4a2-8abfd7d8fbc6
-- title:
--   Leaves: bsum U tau Of
-- statement:
--   bsumU τ k = 2^(betaU k s) for τ = 2^(4s+17).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Leaves.lean#L40-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Leaves.lean#L40-L43

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

theorem UniformInK.Leaves.bsumU_tauOf (k s : ℕ) : bsumU (tauOf s) k = 2 ^ betaU k s := by sorry
