-- Prove2me | Theorems.Thm_SplitCount_hasNil_iff
-- name    : SplitCount.hasNil_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:32:41.914061+00:00
-- url     : https://prove2.me/theorems/83bf5a42-fef3-4d3f-a5f2-1b7bac8f65ff
-- title:
--   Split Count: has Nil iff
-- statement:
--   There is an empty clause exactly if `hasNil` says so.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Suffices.lean#L38-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Suffices.lean#L38-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_SplitCount_Leaf
import Definitions.Def_CountKSat_Walk
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_SplitCount_Suffices
set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify Paper CountKSat Eight Eight.Width Occ

theorem SplitCount.hasNil_iff (ψ : Fml) : hasNil ψ = true ↔ [] ∈ ψ := by sorry
