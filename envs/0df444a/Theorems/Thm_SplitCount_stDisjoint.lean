-- Prove2me | Theorems.Thm_SplitCount_stDisjoint
-- name    : SplitCount.stDisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:36:44.424253+00:00
-- url     : https://prove2.me/theorems/886bfec0-6371-4397-bb36-f3f3b52f9a14
-- title:
--   Split Count: st Disjoint
-- statement:
--   «no two of which share a satisfying assignment», at one node: an assignment satisfies the node
--   exactly if it satisfies one of the two children, and it never satisfies both.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L102-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L102-L120

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Tauto
import Definitions.Def_SplitCount_Disjoint
set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight.Width

theorem SplitCount.stDisjoint : StDisjoint := by sorry
