-- Prove2me | Theorems.Thm_SplitSat_stack_stepN
-- name    : SplitSat.stack_stepN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:27:24.884311+00:00
-- url     : https://prove2.me/theorems/d08810b3-0bbf-4cdd-90ea-e0ff60483b29
-- title:
--   Split Sat: stack step N
-- statement:
--   The stack of the walk with n carried along, after i rounds, is the stack of the walk, with n
--   beside every formula.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L67-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L67-L69

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

theorem SplitSat.stack_stepN (step : Fml → Option (Fml × Fml)) (u : List Unit) (i : ℕ) (x : Fml) :
    ((Sparsify.round (stepN step))^[i] ([((u, x) : NFml)], [])).1 = ((Sparsify.round step)^[i] ([x], [])).1.map fun y => ((u, y) : NFml) := by sorry
