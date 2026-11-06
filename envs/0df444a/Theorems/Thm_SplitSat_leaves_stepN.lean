-- Prove2me | Theorems.Thm_SplitSat_leaves_stepN
-- name    : SplitSat.leaves_stepN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:28:59.018258+00:00
-- url     : https://prove2.me/theorems/011fb6e1-af17-4260-ae85-dba0bcf1c3e4
-- title:
--   Split Sat: leaves step N
-- statement:
--   The leaves of the tree with n carried along are the leaves of the tree, with n beside each.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L34-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L34-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify

theorem SplitSat.leaves_stepN (step : Fml → Option (Fml × Fml)) (u : List Unit) : ∀ (d : ℕ) (x : Fml),
    leaves (stepN step) d (u, x) = (leaves step d x).map fun y => ((u, y) : NFml)
  := by sorry
