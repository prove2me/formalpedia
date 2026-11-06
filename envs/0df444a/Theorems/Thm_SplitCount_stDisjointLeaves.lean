-- Prove2me | Theorems.Thm_SplitCount_stDisjointLeaves
-- name    : SplitCount.stDisjointLeaves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:52:22.312107+00:00
-- url     : https://prove2.me/theorems/21b903b3-4b41-4d06-be4b-f7b662b42701
-- title:
--   Split Count: st Disjoint Leaves
-- statement:
--   «no two of which share a satisfying assignment», for the outputs: no assignment satisfies the
--   formulas of two different leaves of the tree below any node, cut at any depth.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L147-L159
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L147-L159

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

theorem SplitCount.stDisjointLeaves : StDisjointLeaves := by sorry
