-- Prove2me | Theorems.Thm_SplitSat_widthP_eq
-- name    : SplitSat.widthP_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:27:08.24994+00:00
-- url     : https://prove2.me/theorems/22e9440c-a6a7-441e-8f81-2d99115d620b
-- title:
--   Split Sat: width P eq
-- statement:
--   The first part of what the program returns is a number in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Leaf.lean#L37-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Leaf.lean#L37-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_GraphProblems_Engine
import Mathlib.Tactic
import Definitions.Def_SplitSat_Leaf
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Eight.Width GraphProblems

theorem SplitSat.widthP_eq (p : List Unit × Fml) : widthP p = (List.replicate (widthP p).1.length (), (widthP p).2) := by sorry
