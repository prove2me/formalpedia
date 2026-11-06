-- Prove2me | Theorems.Thm_SplitSat_round_stepN_iterate
-- name    : SplitSat.round_stepN_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:29:24.492696+00:00
-- url     : https://prove2.me/theorems/832b99be-ccb5-4b42-bb78-d431e6140073
-- title:
--   Split Sat: round step N iterate
-- statement:
--   The same for any number of rounds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L58-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L58-L63

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

theorem SplitSat.round_stepN_iterate (step : Fml → Option (Fml × Fml)) (u : List Unit) (i : ℕ) (p : List Fml × List Fml) :
    (Sparsify.round (stepN step))^[i] (p.1.map fun y => ((u, y) : NFml), p.2.map fun y => ((u, y) : NFml)) =
      (((Sparsify.round step)^[i] p).1.map fun y => ((u, y) : NFml), ((Sparsify.round step)^[i] p).2.map fun y => ((u, y) : NFml)) := by sorry
