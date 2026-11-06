-- Prove2me | Theorems.Thm_SplitSat_round_stepN
-- name    : SplitSat.round_stepN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:29:44.231332+00:00
-- url     : https://prove2.me/theorems/5dd74ff5-8d49-4311-ab32-37fd50874681
-- title:
--   Split Sat: round step N
-- statement:
--   One round of the walk commutes with putting n beside every formula.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L45-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L45-L55

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

theorem SplitSat.round_stepN (step : Fml → Option (Fml × Fml)) (u : List Unit) (p : List Fml × List Fml) :
    Sparsify.round (stepN step) (p.1.map fun y => ((u, y) : NFml), p.2.map fun y => ((u, y) : NFml)) =
      ((Sparsify.round step p).1.map fun y => ((u, y) : NFml), (Sparsify.round step p).2.map fun y => ((u, y) : NFml)) := by sorry
