-- Prove2me | Theorems.Thm_UniformInK_Leaves_sq_le_of_s0U_le
-- name    : UniformInK.Leaves.sq_le_of_s0U_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:55:24.903837+00:00
-- url     : https://prove2.me/theorems/e0a339a6-190f-40ec-afed-e0337760a6a3
-- title:
--   Leaves: sq le of s0 U le
-- statement:
--   k² ≤ 2^s for s ≥ s0U k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Leaves.lean#L33-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Leaves.lean#L33-L37

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

theorem UniformInK.Leaves.sq_le_of_s0U_le {k s : ℕ} (hs : s0U k ≤ s) : k ^ 2 ≤ 2 ^ s := by sorry
